import Googology.Trans.PoR.InaccPsi.R2.XqTop
import Googology.Trans.PoR.InaccPsi.R2.WrMid
import Googology.Trans.PoR.InaccPsi.R2.RoMove
import Googology.Trans.PoR.InaccPsi.R2.VsBase

/-!
# The base-data move at the base `0` for the small exponents

`Θ = gxTh ρ_λ (ldAtR λ)`, `X = Ω_{k+3}`, `W^x = leWe x`, `Y_X = ψ_{Ω₂}(X)`, `B_n = Bc.bcB S n`, `c_n = L(n+1)`,
"window" = `CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart, `B_n ρ_λ = ρ_{λ'}`.

* `xvOm2_mul` (`Ω₂·Ω_{k+3} = Ω_{k+3}`), `xvShB` (**the shift `Ω_{k+3}` is fixed by every `B_n`**: `Ro.RoShB S X 1`);
* `xvBase0` (**`Ro.RoBaseE λ X e 0` at EVERY `λ` for every `e < Y_X`**: the own clause holds since
  `e' ≤ e < ψ₂(X) ≤ ψ₂(W^{X+e'})`);
* `xvBaseMove0` (**THE BASE-DATA MOVE at the base `0`, small exponents**: at a window, under the moves of the codes
  below `ψ₂(W^{X+e})`, for every code `e < Y_X`: `B_n e` is a code of `λ'` below `Y_X`, `(B_n e, 0)` is a top base of
  `λ'`, and `B_n(0 + W^{X+e}) = 0 + W^{X+B_n e}`);
* `xvTop0Move` (**every top atom `ψ₂(W^{X+e})`, `e < Y_X` a code, moves at every window**: `B_n` of it is the atom
  `ψ₂(W^{X+B_n e})` of `λ'` and `Θ'(B_n s) = B_n Θ(s)`; `Xq.xqTopMove` with the bound `Θ(s) < δ_λ ≤ r(λ)` from
  `Lj.ljTheta_lt_delta`, no extra hypothesis);
* `xvTop0_nonvac` (non-vacuity: `e = 0` meets the code hypotheses at every restart and every `k`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- `Ω₂·Ω_{k+3} = Ω_{k+3}`. -/
theorem xvOm2_mul (k : ℕ) :
    Om (1 + 1 : Ordinal.{0}) * Om ((k : Ordinal.{0}) + 1 + 1 + 1) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
  have h3 : ((k : Ordinal.{0}) + 1 + 1 + 1) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hE : ω ^ Om ((k : Ordinal.{0}) + 1 + 1 + 1) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) :=
    Low.opow_eq_self_of_SC (SC_Om h3)
  have hW := Vn.vnWe_OmK k
  unfold leWe at hW
  exact (opow_right_inj one_lt_omega0).1 (hW.trans hE.symm)

/-- **The shift `Ω_{k+3}` is fixed by every base change** (`Ro.RoShB` with the image `1`). -/
theorem xvShB (k : ℕ) : Ro.RoShB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 1 := by
  refine ⟨one_ne_zero, fun n => ?_⟩
  have hs : (k : Ordinal.{0}) + 1 + 1 < ω := (lt_add_one _).trans (vkNat_lt_omega k)
  obtain ⟨hD, hB⟩ := Vs.vsW_D (S := S) hs (n := n)
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  rw [xvOm2_mul, mul_one]
  exact ⟨hD, hB, hD1, hB1⟩

/-- **`Ro.RoBaseE λ Ω_{k+3} e 0` at every `λ` for every `e < ψ₂(Ω_{k+3})`.** -/
theorem xvBase0 (k : ℕ) (l : Ordinal.{0}) {e : Ordinal.{0}}
    (he : e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1))) :
    Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0 := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (he2.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun _ _ => CSet.zero_mem _ _, fun e' _ he' => ?_⟩
  · rw [zero_add]; exact hwW.trans_le (ConjT.OmW_le_A S _)
  · rw [zero_add]
    refine (he'.trans_lt he).trans_le (psi_mono hκ2 ?_).1
    calc X = leWe X := (Vn.vnWe_OmK k).symm
      _ ≤ leWe (X + e') := leWe_mono le_self_add

section Win

variable {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **The window data**: `ρ_λ < P(η)` with `A = A_{η_λ}` own, `ψ₁(A) = ρ_λ`, and the same at `λ'` with some own `A'`. -/
theorem xvWin :
    upsilon l < Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) ∧
      ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
      S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l ∧
      upsilon l' < Pv S (Om ω + Nc.ncPp S * (ω + 1)) ∧
      ∃ A', A' ∈ S.CSet A' (S.psi A' (Om 1)) ∧ S.psi A' (Om 1) = upsilon l' := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  have hρA : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hown0 : ConjT.Aη S (cdEta S l) + 0 ∈
      S.CSet (ConjT.Aη S (cdEta S l) + 0) (S.psi (ConjT.Aη S (cdEta S l) + 0) (Om 1)) := by
    rw [add_zero]; exact hown
  have hhi0 : S.psi (ConjT.Aη S (cdEta S l) + 0) (Om 1) < Bc.bcC S (n + 1) := by
    rw [add_zero, hρA]; exact h2
  obtain ⟨A', hA', hBP, -⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hD0 hown0 hhi0
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  exact ⟨hX, hown, hρA, hX', A', hA', hρA'⟩

/-- **THE BASE-DATA MOVE at the base `0` for the small exponents** `e < ψ₂(Ω_{k+3})`. -/
theorem xvBaseMove0 (k : ℕ) {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (heY : e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S e ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧ Bc.bcB S n e < Om (1 + 1) ∧
      Bc.bcB S n e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ∧
      Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n e) 0 ∧
      MvD S (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) ∧
      Bc.bcB S n (0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
        0 + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, -, -, -, -⟩ := xvWin hR h1 hr hl' hB
  have hY2 : S.psi X (Om (1 + 1)) ≤ S.psi (leWe (X + e)) (Om (1 + 1)) := by
    refine (psi_mono hκ2 ?_).1
    calc X = leWe X := (Vn.vnWe_OmK k).symm
      _ ≤ leWe (X + e) := leWe_mono le_self_add
  have hes : e < S.psi (leWe (X + e)) (Om (1 + 1)) := heY.trans_le hY2
  have he2 : e < Om (1 + 1) := heY.trans (psi_lt hκ2 _)
  obtain ⟨hDe, hBec, hBeP, -, -⟩ := IH e hec hes
  -- `B_n e < ψ₂(X)`
  have hs : (k : Ordinal.{0}) + 1 + 1 < ω := (lt_add_one _).trans (vkNat_lt_omega k)
  obtain ⟨hDX, hBX⟩ := Vs.vsW_D (S := S) hs (n := n)
  obtain ⟨hDY, hBY⟩ := mxB_atom (n := n) hDX (Vn.vnOmK3_mem k _ _)
  rw [hBX] at hBY
  have hBeY : Bc.bcB S n e < S.psi X (Om (1 + 1)) := by
    have h := (mvB_lt_iff (k := n) hDe hDY).2 heY
    rwa [hBY] at h
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
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (xvShB (S := S) k) P hPD hPdec hPW
    ⟨hec, hes, he2⟩ ⟨hec, hes, he2⟩
  refine ⟨hDe, hBec, hBeP.trans Lj.ljThP_lt_Om2, hBeY, xvBase0 k l' hBeY, hDW, ?_⟩
  rw [zero_add, zero_add, hBW]

/-- **Every top atom `ψ₂(W^{Ω_{k+3}+e})` with a code `e < ψ₂(Ω_{k+3})` moves at every window** (under the moves of
the codes below it, the premise of the wall). -/
theorem xvTop0Move (k : ℕ) {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (heY : e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)))
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
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', A', hA', hρA'⟩ := xvWin hR h1 hr hl' hB
  obtain ⟨-, hBec, hBe2, -, hb', -, hmv⟩ := xvBaseMove0 hR h1 hr hl' hB k hec heY IH
  have he2 : e < Om (1 + 1) := heY.trans (psi_lt hκ2 _)
  have hb := xvBase0 (S := S) k l heY
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hwW : ∀ e', e' < Om (1 + 1) → leWe (X + e') < Om ω := fun e' he' =>
    (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal hXW (he'.trans ldOm2_lt_OmW))).1
  -- the bound `Θ(ψ₂ t) < c_{n+1}`
  have hsθ : S.psi (0 + leWe (X + e)) (Om (1 + 1)) ≤ Lj.ljThP S := by
    rw [zero_add]
    exact ((psi_mono hκ2 (hwW e he2).le).1).trans Lj.ljTh_lt_ThP.le
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
  -- the image is an atom of `λ'`
  have hX'' := hX'
  have hBeH : Bc.bcB S n e ∈ cdHull S l' := (ldHull_iff hl' hX'' hBe2).2 hBec
  have hatom : S.psi (leWe (X + Bc.bcB S n e)) (Om (1 + 1)) ∈ ldAtR S l' :=
    ⟨leWe (X + Bc.bcB S n e), leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) hBeH),
      (hwW _ hBe2).trans_le (ConjT.OmW_le_A S _), rfl⟩
  exact ⟨hDs, hBs, hBs ▸ hatom, hmove⟩

end Win

/-- **Non-vacuity**: the code hypotheses of `xvBaseMove0` / `xvTop0Move` hold at `e = 0` at every restart and every
level `k`, and `(0, 0)` is a top base there. -/
theorem xvTop0_nonvac (k : ℕ) {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    GxCl (upsilon l) (ldAtR S l) 0 ∧ (0 : Ordinal.{0}) < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hpos : (0 : Ordinal.{0}) < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) :=
    (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  exact ⟨GxCl.zero hρSC.1, hpos, xvBase0 k l hpos⟩

end Googology.Trans.PoR.InaccPsi.R2.Xv

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvOm2_mul
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvShB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvBase0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvWin
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvBaseMove0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvTop0Move
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xv.xvTop0_nonvac
