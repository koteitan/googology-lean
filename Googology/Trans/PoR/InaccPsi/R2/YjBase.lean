import Googology.Trans.PoR.InaccPsi.R2.YdMoveB

/-!
# The two base facts at `λ'` for a top base `(e, β)`, `β ∈ D`

`X = Ω_{k+3}`, `W^x = leWe x = ω^{Ω₂·x}`, `t = β + W^{X+e}`, `B_n = Bc.bcB S n`, "window" as in `Yd.ydBaseMove`,
"IH" the premise of the wall statement at `ψ₂ t` (every code `x < ψ₂ t` of `λ` moves).

* `yjParts` (the leading exponent and the remainder of a member of `D ∩ Cl(a, b)` are members);
* `yjDvd` (**THE DIVISIBILITY MOVES**: at a window, for a top base `(e, β)`, `β ∈ D`, under IH, every
  `x ∈ D ∩ Cl(t, ψ₂ t)` with `W^{X+e} ∣ x` has `W^{X+B_n e} ∣ B_n x`; one induction on the Cantor normal form of `x`,
  `B_n(ω^L·m + r) = ω^{B_n L}·m + B_n r` (`Ld.ldB_opow`, `Vb.vbB_mulNat`, `Mv.mvB_add`) and
  `B_n(W^{X+e}) = W^{X+B_n e}` (`Ro.roB_We`), so the exponent bound `Ω₂·(X+e) ≤ L` moves to `Ω₂·(X+B_n e) ≤ B_n L`);
* `yjD` (**`B_n β ∈ D_{λ'}`**: `B_n β = κ_{λ'}(B_n(T_λ β))` (`Vb.vbT_move`), so `B_n β < Ω_ω` (`Rx.rxL_lt_OmW`) and
  `B_n β ∈ H_{λ'}` (`Rx.rxL_memH`: every code of `λ'` below `Ω₂` is in the hull); `B_n β ∈ Cl(Ω_ω, θ)` from the
  normality of `B_n β` (`Yd.ydNormB`) and `ψ₂(B_n β) ≤ θ`);
* `yjBaseFacts` (**THE TWO BASE FACTS**, the skeleton node `skBaseFactsB`);
* `yjNonvac` (non-vacuity at `(e, β) = (0, Ω_{k+3}·j)`: the `λ`-side hypotheses hold at every `λ`, so the
  theorems apply beyond `Yd.ydNonvacB`'s base `Ω_{k+3}`), `yjNonvacW` (the same at `(0, Ω_{k+3}·ω)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- The leading exponent and the remainder of a member of `D ∩ Cl(a, b)` are members. -/
theorem yjParts {l a b x : Ordinal.{0}} (hx : VbD S l x) (hxC : x ∈ S.CSet a b) :
    (VbD S l (log ω x) ∧ log ω x ∈ S.CSet a b) ∧
      (VbD S l (x % ω ^ log ω x) ∧ x % ω ^ log ω x ∈ S.CSet a b) :=
  ⟨⟨⟨(rxCDec x hx.1).2, (rxCDec x hx.2.1).2, (log_le_self ω x).trans_lt hx.2.2⟩, (rxCDec x hxC).2⟩,
    ⟨⟨vbC_rem hx.1, vbC_rem hx.2.1, (Ordinal.mod_le _ _).trans_lt hx.2.2⟩, vbC_rem hxC⟩⟩

section Win

variable {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **THE DIVISIBILITY MOVES**: `W^{X+e} ∣ x ⇒ W^{X+B_n e} ∣ B_n x` for every `x ∈ D ∩ Cl(t, ψ₂ t)`. -/
theorem yjDvd (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbD S l x →
      x ∈ S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))
        (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) →
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) ∣ x →
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) ∣ Bc.bcB S n x := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := Yd.ydBaseE_lt k hβD hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec le_rfl
  -- `B_n W^{X+e} = W^{X+B_n e}`
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (β + leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB (S := S) k) P hPD hPdec hPW
    ⟨hec, hes, he2⟩ ⟨hec, hes, he2⟩
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := yjParts hxD hxC
  obtain ⟨hDL, -, -⟩ := hTM _ hLD hLC
  obtain ⟨hDr, -, -⟩ := hTM _ hrD hrC
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * m + x % ω ^ log ω x := by
    rw [← hm]; exact (Ordinal.div_add_mod x _).symm
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hBx
  rw [hBx, hBom, hBo]
  -- the exponent bound `Ω₂·(X+e) ≤ L` and its move
  have hWle : ω ^ (Om (1 + 1) * (X + e)) ≤ x := Ordinal.le_of_dvd hx0 hdv
  have hpL : Om (1 + 1) * (X + e) ≤ log ω x := (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 hWle
  have hWo : leWe (X + e) ≤ ω ^ log ω x := opow_le_opow_right omega0_pos hpL
  have hBWo : Bc.bcB S n (leWe (X + e)) ≤ Bc.bcB S n (ω ^ log ω x) := by
    rcases hWo.lt_or_eq with h | h
    · exact ((mvB_lt_iff hDW hDo).2 h).le
    · rw [h]
  rw [hBW, hBo] at hBWo
  have hp' : Om (1 + 1) * (X + Bc.bcB S n e) ≤ Bc.bcB S n (log ω x) :=
    (opow_le_opow_iff_right one_lt_omega0).1 hBWo
  refine dvd_add (Dvd.dvd.mul_right (opow_dvd_opow ω hp') _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have h2 : leWe (X + e) ∣ ω ^ log ω x * m := Dvd.dvd.mul_right (opow_dvd_opow ω hpL) _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv

/-- **`B_n β ∈ D_{λ'}`** for every top base `(e, β)`, `β ∈ D`, at a window, under IH. -/
theorem yjD (k : ℕ) {e β : Ordinal.{0}} (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    VbD S l' (Bc.bcB S n β) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set a := β + leWe (X + e) with hadef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hβC : β ∈ S.CSet a (S.psi a (Om (1 + 1))) := hb.2.2.2.1 _ le_rfl
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 a) (hρ1.trans (psiS_bounds (S := S) a 1).1)
  obtain ⟨hDβ, -, hBE, hK, -⟩ := vbT_move (n := n) hl hX hl' hX' hSC hTW (Xq.xqLeaf hl hX hl' hX' IH) hβD
    (Xq.xqTE hl hX hown hρA β hβD hβC)
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  have hlt : Bc.bcB S n β < Om ω := by
    rw [← hK]; exact rxL_lt_OmW hZ' hZ1' (ldAt_GxAt _ _) hBE
  have hH : Bc.bcB S n β ∈ cdHull S l' := by
    rw [← hK]
    show _ ∈ S.CSet (ConjT.Aη S (cdEta S l')) (upsilon l')
    refine rxL_memH hZ' hZ1' (ldAt_GxAt _ _) (vbW_SC hl' hX') le_rfl (ConjT.OmW_le_A S _)
      (fun g hg => ?_) _ hBE
    have hg' : g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hg
    obtain ⟨hc, hc2, -⟩ := Ru.ruInv_spec hg'
    exact (ldHull_iff hl' hX' hc2).2 hc
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := hb.2.2.2.1 0 zero_le; rwa [add_zero] at h
  have hn' := Yd.ydNormB n hDβ hβn
  exact ⟨hH, (psi_mono hκ2 hlt.le).2 hn', hlt⟩

/-- **THE TWO BASE FACTS** at `λ'` for a top base `(e, β)`, `β ∈ D`, at a window, under IH:
`W^{X+B_n e} ∣ B_n β` and `B_n β ∈ D_{λ'}`. -/
theorem yjBaseFacts (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) ∣ Bc.bcB S n β ∧ VbD S l' (Bc.bcB S n β) :=
  ⟨yjDvd hR h1 hr hl' hB k hec hβD hb IH β hβD (hb.2.2.2.1 _ le_rfl) hb.1, yjD hR h1 hr hl' hB k hβD hb IH⟩

/-- **EVERY TOP ATOM `ψ₂(β + W^{X+e})` MOVES** at a window under IH (no further hypothesis). -/
theorem yjTopMove (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) := by
  obtain ⟨hdv, hD'⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hb IH
  exact Yd.ydTopMoveB hR h1 hr hl' hB k hec hβD hb IH hdv hD'

end Win

/-- **NON-VACUITY**: `(e, β) = (0, Ω_{k+3}·j)` is a top base in `D` at every `λ`. -/
theorem yjNonvac (k : ℕ) (l : Ordinal.{0}) (j : ℕ) :
    VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) * j) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1) * j) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hW : leWe (X + 0) = X := by rw [add_zero]; exact Vn.vnWe_OmK k
  have hmem : ∀ a c, X * (j : Ordinal.{0}) ∈ S.CSet a c := fun a c =>
    ConjT.mul_nat_mem S (Vn.vnOmK3_mem k a c) j
  have hXj : X * (j : Ordinal.{0}) < Om ω := vbMulNat_lt vkOmW.1.isPrincipal (hXW.trans_le' zero_le) hXW j
  refine ⟨⟨hmem _ _, hmem _ _, hXj⟩, ⟨by rw [hW]; exact dvd_mul_right _ _, hmem _ _, ?_, fun d _ => hmem _ _,
    fun e' _ he' => ?_⟩⟩
  · rw [hW]
    exact (vkOmW.1.isPrincipal hXj hXW).trans_le (ConjT.OmW_le_A S _)
  · have he0 : e' = 0 := le_antisymm he' zero_le
    subst he0
    exact (SC_psi hκ2 _).1

/-- **NON-VACUITY (REFUTE-FIRST point `β = Ω_{k+3}·ω`)**: `(e, β) = (0, Ω_{k+3}·ω)` is a top base in `D` at every `λ`. -/
theorem yjNonvacW (k : ℕ) (l : Ordinal.{0}) :
    VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) * ω) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1) * ω) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hW : leWe (X + 0) = X := by rw [add_zero]; exact Vn.vnWe_OmK k
  have hXS : SC X := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have heq : X * ω = ω ^ (X + 1) := by rw [opow_add, opow_one, Low.opow_eq_self_of_SC hXS]
  have hmem : ∀ a c, X * ω ∈ S.CSet a c := fun a c => by
    rw [heq]
    have := CSet.phi_mem (S := S) (CSet.zero_mem a c) (CSet.succ_mem (Vn.vnOmK3_mem k a c))
    rwa [veblen_zero_apply] at this
  have hXw : X * ω < Om ω := by
    rw [heq]; exact ldOpow_lt_SC vkOmW.1 (vkOmW.1.isPrincipal hXW (one_lt_omega0.trans (omega0_lt_Om omega0_ne_zero)))
  refine ⟨⟨hmem _ _, hmem _ _, hXw⟩, ⟨by rw [hW]; exact dvd_mul_right _ _, hmem _ _, ?_, fun d _ => hmem _ _,
    fun e' _ he' => ?_⟩⟩
  · rw [hW]
    exact (vkOmW.1.isPrincipal hXw hXW).trans_le (ConjT.OmW_le_A S _)
  · have he0 : e' = 0 := le_antisymm he' zero_le
    subst he0
    exact (SC_psi hκ2 _).1

end Googology.Trans.PoR.InaccPsi.R2.Yj

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjParts
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjDvd
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjD
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjBaseFacts
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjTopMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjNonvac
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yj.yjNonvacW
