import Googology.Trans.PoR.InaccPsi.R2.YdPlat
import Googology.Trans.PoR.InaccPsi.R2.XvTop0

/-!
# The base-data move at the base `0` for EVERY top exponent

`X = Ω_{k+3}`, `W^x = leWe x`, `e_m = Yd.ydE S X m` (`e_0 = 0`, `e_{m+1} = ψ₂(W^{X+e_m})`), `E_X = ψ₂(W^{X+Ω₂})`,
`B_n = Bc.bcB S n`, `c_n = L(n+1)`, "window" = `CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart,
`B_n ρ_λ = ρ_{λ'}`.

* `ydTopAt` (**`E_X` is an atom of every `λ`**), `ydBaseE_iff` (**`Ro.RoBaseE λ X e 0 ⇔ e < E_X`, at every `λ`**:
  the own clause fails at the code `E_X`, and holds below it by the plateau `Yd.ydOwn_iff`);
* `ydFix` (**every `B_n` fixes every iterate `e_m`**, and `MvD e_m`);
* `ydBaseMove` (**THE BASE-DATA MOVE at the base `0` for every top base `(e, 0)`**: at a window, under the moves of
  the codes below `ψ₂(W^{X+e})`, `B_n e` is a code of `λ'`, `(B_n e, 0)` is a top base of `λ'` and
  `B_n(0 + W^{X+e}) = 0 + W^{X+B_n e}`; NO inverse correspondence is used: `e < e_m` for some `m`, so
  `B_n e < B_n e_m = e_m`, and the own clause at `λ'` holds for every ORDINAL below `e_m`);
* `ydTopMove` (**every top atom `ψ₂(W^{X+e})` over the base `0` moves at every window**, with no extra hypothesis);
* `ydE_code`, `ydNonvac` (non-vacuity: every iterate `e_m` is a code and a top exponent at every restart; `e_1 = ψ₂(X)`,
  `e_2`, … lie outside the range `e < ψ₂(X)` of `Xv.xvBaseMove0`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

theorem ydX_mem (k : ℕ) : ∀ a b : Ordinal.{0}, Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∈ S.CSet a b :=
  fun a b => Vn.vnOmK3_mem k a b

theorem ydW_lt (k : ℕ) {e : Ordinal.{0}} (he : e ≤ Om (1 + 1)) :
    leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) < Om ω := by
  have hXW : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := Wv.wvOmK_lt_W k
  have he' : e < Om ω := he.trans_lt ldOm2_lt_OmW
  exact (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal hXW he')).1

/-- **`E_X = ψ₂(W^{X+Ω₂})` is an atom of every `λ`.** -/
theorem ydTopAt (k : ℕ) (l : Ordinal.{0}) :
    S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ∈ ldAtR S l :=
  ⟨_, leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) (mxOm2_mem _ _)),
    (ydW_lt k le_rfl).trans_le (ConjT.OmW_le_A S _), rfl⟩

/-- **`Ro.RoBaseE λ X e 0 ⇔ e < E_X`** at every `λ`. -/
theorem ydBaseE_iff (k : ℕ) (l e : Ordinal.{0}) :
    Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0 ↔
      e < S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h1 := h.2.2.2.2 _ (GxCl.atom (ydTopAt k l)) hc
    rw [zero_add] at h1
    exact absurd (h1.trans_le ydTop_fail) (lt_irrefl _)
  · intro he
    have he2 : e < Om (1 + 1) := he.trans (psi_lt (InR_Om_succ 1) _)
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun _ _ => CSet.zero_mem _ _, fun e' _ he' => ?_⟩
    · rw [zero_add]; exact (ydW_lt k he2.le).trans_le (ConjT.OmW_le_A S _)
    · rw [zero_add]; exact (ydOwn_iff (ydX_mem k) e).2 he e' he'

/-- **Every `B_n` fixes every iterate `e_m`.** -/
theorem ydFix (k n : ℕ) : ∀ m, MvD S (ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) m) ∧
    Bc.bcB S n (ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) m) = ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) m
  | 0 => by
    rw [ydE_zero]
    have hc : (0 : Ordinal.{0}) < Bc.bcC S n := (Lw.lw_L_SC S _).1
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_fix' S n 0 hc⟩
  | m + 1 => by
    set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
    obtain ⟨hDm, hBm⟩ := ydFix k n m
    have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
    set P : Ordinal.{0} → Prop := fun x => x = 0 ∨ (x = ydE S X m ∧ SC x) with hP
    have hPD : ∀ x, P x → MvD S x := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact mvD_of_lt (Lw.lw_L_SC S ω).1
      · exact hDm
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := by
      rintro x (rfl | ⟨hx, hxS⟩) hx0
      · exact absurd rfl hx0
      · have hl : log ω x = x := by
          conv_lhs => rw [← gg_SC_eps hxS]
          exact log_opow one_lt_omega0 x
        rw [hl, gg_SC_eps hxS, Ordinal.sub_self]
        exact ⟨Or.inr ⟨hx, hxS⟩, Or.inl rfl⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact ldOm2_SC.1
      · exact ydE_lt_Om2 X m
    have hPm : P (ydE S X m) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨rfl, ydE_SC X j⟩
    obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB (S := S) k) P hPD hPdec hPW hPm hPm
    rw [hBm] at hBW
    have hown : leWe (X + ydE S X m) ∈ S.CSet (leWe (X + ydE S X m)) (S.psi (leWe (X + ydE S X m)) (Om (1 + 1))) := by
      refine leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt ?_))
      rw [← ydE_succ]; exact ydE_lt_succ (ydX_mem k) m
    obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDW hown
    rw [hBW] at hBs
    rw [ydE_succ]
    exact ⟨hDs, hBs⟩

/-- **Every iterate is in every hull `Cl(A, ρ)` with `Ω_ω ≤ A`.** -/
theorem ydE_mem (k : ℕ) {A ρ : Ordinal.{0}} (hA : Om ω ≤ A) :
    ∀ m, ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) m ∈ S.CSet A ρ
  | 0 => by rw [ydE_zero]; exact CSet.zero_mem _ _
  | m + 1 => by
    rw [ydE_succ]
    exact CSet.psi_mem ((ydW_lt k (ydE_lt_Om2 _ m).le).trans_le hA) (InR_Om_succ 1) (mxOm2_mem _ _)
      (leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) (ydE_mem k hA m)))

/-- **NON-VACUITY: every iterate `e_m` is a code and a top exponent at the base `0` at every `λ`**, and `e_{m+1}`
is not below `ψ₂(X)` (so it lies outside the range of `Xv.xvBaseMove0`). -/
theorem ydNonvac (k : ℕ) (l : Ordinal.{0}) (m : ℕ) :
    GxCl (upsilon l) (ldAtR S l) (ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (m + 1)) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (m + 1)) 0 ∧
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ≤ ydE S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (m + 1) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  refine ⟨GxCl.atom ⟨leWe (X + ydE S X m), leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _)
      (ydE_mem k (ConjT.OmW_le_A S _) m)), (ydW_lt k (ydE_lt_Om2 _ m).le).trans_le (ConjT.OmW_le_A S _), rfl⟩,
    (ydBaseE_iff k l _).2 ((ydE_lt_succ (ydX_mem k) (m + 1)).trans_le (ydE_le_top X (m + 2))), ?_⟩
  rw [ydE_succ]
  refine (psi_mono (InR_Om_succ 1) ?_).1
  calc X = leWe X := (Vn.vnWe_OmK k).symm
    _ ≤ leWe (X + ydE S X m) := leWe_mono le_self_add

section Win

variable {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **THE BASE-DATA MOVE at the base `0` for every top base `(e, 0)`.** -/
theorem ydBaseMove (k : ℕ) {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S e ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧ Bc.bcB S n e < Om (1 + 1) ∧
      Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n e) 0 ∧
      MvD S (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) ∧
      Bc.bcB S n (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
        0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hl := hR.1
  obtain ⟨hX, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he : e < S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) := (ydBaseE_iff k l e).1 hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt (InR_Om_succ 1) _)
  obtain ⟨m, hm⟩ := ydLt_top (ydX_mem k) he
  have hes : e < S.psi (leWe (X + e)) (Om (1 + 1)) := ydOwn m e hm
  obtain ⟨hDe, hBec, hBeP, -, -⟩ := IH e hec hes
  obtain ⟨hDm, hBm⟩ := ydFix (S := S) k n m
  have hBem : Bc.bcB S n e < ydE S X m := by
    have h := (mvB_lt_iff (k := n) hDe hDm).2 hm
    rwa [hBm] at h
  have hBeE : Bc.bcB S n e < S.psi (leWe (X + Om (1 + 1))) (Om (1 + 1)) := hBem.trans_le (ydE_le_top X m)
  -- the class of the codes below `ψ₂(W^{X+e})`
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
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
  refine ⟨hDe, hBec, hBeP.trans Lj.ljThP_lt_Om2, (ydBaseE_iff k l' _).2 hBeE, hDW, ?_⟩
  rw [zero_add, zero_add, hBW]

/-- **Every top atom `ψ₂(W^{X+e})` over the base `0` moves at every window** (under the moves of the codes below
it, the premise of the wall; no base-data or bound hypothesis). -/
theorem ydTopMove (k : ℕ) {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) =
        S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', A', hA', hρA'⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨-, hBec, hBe2, hb', -, hmv⟩ := ydBaseMove hR h1 hr hl' hB k hec hb IH
  have he2 : e < Om (1 + 1) := ((ydBaseE_iff k l e).1 hb).trans (psi_lt hκ2 _)
  -- the bound `Θ(ψ₂ t) < c_{n+1}`
  have hsθ : S.psi (0 + leWe (X + e)) (Om (1 + 1)) ≤ Lj.ljThP S := by
    rw [zero_add]
    exact ((psi_mono hκ2 (ydW_lt k he2.le).le).1).trans Lj.ljTh_lt_ThP.le
  have hhi : gxTh (upsilon l) (ldAtR S l) (S.psi (0 + leWe (X + e)) (Om (1 + 1))) < Bc.bcC S (n + 1) := by
    rw [← ldTheta hl hX (hsθ.trans Lj.ljThP_lt_Om2.le)]
    exact ((Lj.ljTheta_lt_delta hl hX hown hsθ).trans_le (cdR_ge S l)).trans hr
  have IH' : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (0 + leWe (X + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x) :=
    fun x hx hxs => IH x hx (by rwa [zero_add] at hxs)
  obtain ⟨hDs, hBs, hmove⟩ := Xq.xqTopMove hl hX hl' hX' hown hρA hA' hρA' h1.le hB k hec he2 (Xi.xiD_zero l) hb
    hBec hBe2 (Xi.xiD_zero l') hb' hmv IH' hhi
  rw [zero_add] at hDs hBs hmove
  rw [zero_add] at hBs
  have hBeH : Bc.bcB S n e ∈ cdHull S l' := (ldHull_iff hl' hX' hBe2).2 hBec
  have hatom : S.psi (leWe (X + Bc.bcB S n e)) (Om (1 + 1)) ∈ ldAtR S l' :=
    ⟨leWe (X + Bc.bcB S n e), leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) hBeH),
      (ydW_lt k hBe2.le).trans_le (ConjT.OmW_le_A S _), rfl⟩
  exact ⟨hDs, hBs, hBs ▸ hatom, hmove⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTopAt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydBaseE_iff
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydFix
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydE_mem
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydNonvac
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydBaseMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTopMove
