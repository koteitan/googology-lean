import Googology.Trans.PoR.InaccPsi.R2.ZqSt
import Googology.Trans.PoR.InaccPsi.R2.UxRoad
import Googology.Trans.PoR.InaccPsi.R2.YyY3

/-!
# Level systems past `Γ₂` over the base `Ω_ω`: every atom below `ψ_{Ω₂}(Ω_ω + Y₃)` moves

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `Y₃ = ψ_{Ω₃}(Ω₃)` (`Ug.ugY`),
`Y₂ = ψ_{Ω₂}(Ω₂)` (`Uj.ujY S 0`), a level system past `Γ₂` `Uu.UuLS S λ E_b Th Uu.uuOw` with its move
`Ux.UxLSB`, the family `Uu.uuShG`.

As in `Zq.zqRepSt`, the closure condition of the level read off the digit part `d'` of the atom argument
`Ω_ω + d'` follows from `Ux.uxExtrRem` (`W^{W^E} ∣ Ω_ω`), and the code levels `E < Ω₂` lie below some
`EX_j = Rw.rwEX S 0 Ω_ω j` (`Ux.uxEX_own` at the base `Ω_ω`).

* `zqRepUx` (**every atom `θ < s < T_{W^{E_b}}(Ω_ω)` is `ψ_{Ω₂}(Ω_ω + c)`, own over `Ω_ω`**), `zqReadUx`
  (**`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`, `v < Y₂`**);
* `zqAtMoveUx` (**every atom `θ < s < K ≤ T_{W^{E_b}}(Ω_ω)` moves**, `B_n K = K`, for every system past `Γ₂`);
* `zqB_Y` (`B_n ψ_{Ω₂}(Ω_ω + Y₃) = ψ_{Ω₂}(Ω_ω + Y₃)`), `zqAtK_Y` (**`Zj.ZjAtK S ψ_{Ω₂}(Ω_ω + Y₃)`**, from the
  system `Uu.uuLSY` with its move `Ux.uxLSB_Y`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ux
  Googology.Trans.PoR.InaccPsi.R2.Zj

variable {S : InaccSeq.{0}} {Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}

theorem zqY_lt_OmW : ugY S < Om ω := ugY_lt_Om3.trans Ry.ryOm3_lt

/-- A shift past `Γ₂` over `Ω_ω` has `X + Ω₂ < Ω_ω`. -/
theorem zqX_WY {l X : Ordinal.{0}} (h : X = 0 ∨ ∃ Xh, UjSh S l (Om ω) X Xh) : X + Om (1 + 1) < Om ω := by
  rcases h with rfl | ⟨Xh, h⟩
  · rw [zero_add]; exact ldOm2_lt_OmW
  · exact h.ltY.trans zqY_lt_OmW

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l)) (hS : UuLS S l Eb Th (uuOw S))

include hl hX hown hAW hS

/-- **Every atom `θ < s < T_{W^{E_b}}(Ω_ω)` of a level system past `Γ₂` is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)`
own over `Ω_ω`** (family `Uu.uuShG S λ E_b Th Uu.uuOw`). -/
theorem zqRepUx (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hθs : ConjT.th S < s)
    (hsK : s < S.psi (Om ω + leWe (leWe Eb)) (Om (1 + 1))) :
    ∃ X e c v, (X = 0 ∨ ∃ Xh, uuShG S l Eb Th (uuOw S) (Om ω) X Xh) ∧
      RwOwn S l (uuShG S l Eb Th (uuOw S)) X e (Om ω) c v ∧ RoBaseE S l X e (Om ω) ∧
      s = S.psi (Om ω + c) (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hY := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  obtain ⟨d, rfl, hnf, hdH, -⟩ := snNf hs hρ1.le
  have hWd : Om ω < d := by
    by_contra h
    push Not at h
    exact absurd hθs (not_lt.2 (psi_mono (S := S) hκ h).1)
  set d' := d - Om ω with hd'_def
  have hdd : d = Om ω + d' := (Ordinal.add_sub_cancel_of_le hWd.le).symm
  have hd'0 : d' ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hdd
    exact absurd hdd hWd.ne'
  have hEbW : Eb < Om ω := hS.leY.trans_lt zqY_lt_OmW
  have hd'ε : d' < leWe (leWe Eb) := by
    by_contra h
    push Not at h
    have h2 : Om ω + leWe (leWe Eb) ≤ d := by rw [hdd]; exact (add_le_add_iff_left _).2 h
    exact absurd hsK (not_lt.2 (psi_mono (S := S) hκ h2).1)
  rw [hdd] at hnf hdH hs hθs ⊢
  set Y := log ω d' / Om (1 + 1) with hY_def
  set E := log ω Y / Om (1 + 1) + 1 with hE_def
  have hYlt : Y < leWe Eb := by
    have h1 : leWe 0 ≤ d' := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hd'0
    exact (sjLogW h1 hd'ε).2
  have hlY : log ω Y / Om (1 + 1) < Eb := by
    rcases eq_or_ne Y 0 with h0 | hY0
    · rw [h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hS.lim.ne_bot
    · have h1 : leWe 0 ≤ Y := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hY0
      exact (sjLogW h1 hYlt).2
  have hE : E < Eb := hS.lim.succ_lt hlY
  have hEY : E < ugY S := hE.trans_le hS.leY
  have he1 : 1 ≤ E := le_add_self
  have hdW : d' < leWe (leWe E) := by
    refine (roLt_We_log d').trans_le (leWe_mono ?_)
    exact Order.add_one_le_of_lt (roLt_We_log Y)
  have hWEY : leWe E < ugY S := (leWe_lt_SC hY hWY hEY).1
  have hKdvd : leWe (leWe E) ∣ Om ω := zjWX_dvd (hWEY.trans zqY_lt_OmW)
  have hd'H : d' ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := snHullRem hdH hKdvd hdW
  have hst : S.psi (Om ω + d') (Om (1 + 1)) < S.psi (Om ω + leWe (0 + leWe E)) (Om (1 + 1)) := by
    rw [zero_add]; exact psi_lt_psi hκ ((add_lt_add_iff_left _).2 hdW) hnf
  have hcl3 : UgCL S E (Om ω) 0 := by
    intro Q hQ hQ'
    have htQ := hst.le.trans hQ'
    have hdQ : UgC S (1 + 1) Q d' := uxExtrRem hnf hKdvd hdW hWEY hQ htQ
    exact UgC.add (uxLogW hQ (uxLogW hQ hdQ)) (UgC.small (gg_one_lt_of_SC hQ))
  have hcl : uuOw S E (Om ω) 0 := by
    rcases lt_or_ge E (Om (1 + 1)) with hEW | hEW
    · refine Or.inl ⟨hEW, ?_⟩
      have hTE : E < S.psi (Om ω + leWe (0 + leWe E)) (Om (1 + 1)) :=
        uxCode_lt (SC_psi (InR_Om_succ 1) _) (hcl3 _ (SC_psi (InR_Om_succ 1) _) le_rfl) hEW
      exact uxEX_own (X0 := 0) (β := Om ω) (fun d _ => zjOmW_own d) (CSet.zero_mem _ _)
        (by rw [zero_add]; exact zjWX_dvd (roWe_lt_OmW ldOm2_lt_OmW))
        (fun Q hQ _ => UgC.zero hQ.1) (by rw [zero_add]; exact (leWe_lt_SC hY hWY hWY).1) hEW hTE
    · exact Or.inr ⟨hEW, hcl3⟩
  have hEH : E ∈ cdHull S l :=
    CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem (ldDivK_mem ldOm2_SC (leLog_mem hd'H))))
  have hEW : 0 + leWe E < Om ω := by rw [zero_add]; exact hWEY.trans zqY_lt_OmW
  have hb : RoBaseE S l (0 + leWe E) 0 (Om ω) := zjBaseX hAW hEW
  have hcls := uxClsLev_all hl hX hS E hEH he1 hE (Om ω) 0 0 (Or.inl ⟨rfl, rfl⟩) hcl (Om ω) le_rfl hb
    (zjRd hl hX hown hAW)
  have htT : S.psi (Om ω + d') (Om (1 + 1)) < leTe S (0 + leWe E + 0) (Om ω) := by
    rw [add_zero]; exact hst
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hownc, hbo, e1⟩
  · exact absurd hθs (not_lt.2 h)
  · exact ⟨X', e', c, v, Rw.rwOwn_sh hownc, hownc, hbo, e1⟩

/-- **`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`, `v < Y₂`** for every own `(X, e, c, v)` over `Ω_ω`. -/
theorem zqReadUx {X e c v : Ordinal.{0}} (hownc : RwOwn S l (uuShG S l Eb Th (uuOw S)) X e (Om ω) c v)
    (hb : RoBaseE S l X e (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
      ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧ c < leWe (X + e) ∧ v < ujY S 0 :=
  uuOwnRead hl hX (uuShG_sh hl hX hS) hownc _ hb (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)

end Main

/-- **Every atom `θ < s < K` moves** once the codes below it move, for a level system past `Γ₂` at every restart
index with its move, and a bound `K ≤ T_{W^{E_b}}(Ω_ω)` fixed by `B_n`. -/
theorem zqAtMoveUx
    (hSys : ∀ l ηx, IsRestartIdx l → upsilon l < Pv S ηx → UuLS S l Eb Th (uuOw S))
    (hMv : ∀ n l l' ηx ηx', IsRestartIdx l → upsilon l < Pv S ηx → IsRestartIdx l' → upsilon l' < Pv S ηx' →
      UxLSB S n l l' Eb Th)
    {n : ℕ} {l l' K : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (hKE : K ≤ S.psi (Om ω + leWe (leWe Eb)) (Om (1 + 1))) (hKB : MvD S K ∧ Bc.bcB S n K = K)
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hθs : ConjT.th S < s) (hsK : s < K)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < K ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  obtain ⟨hX, hX', hown, hown', -, -, -, -, hBψ⟩ := Wr.wrWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hS := hSys l _ hl hX
  have hS' := hSys l' _ hl' hX'
  have hSh := uuShG_sh hl hX hS
  have hSh' := uuShG_sh hl' hX' hS'
  rcases zqRepUx hl hX hown hAW hS s hs hθs (hsK.trans_le hKE) with ⟨X, e, c, v, hXs, hownc, hb, rfl⟩
  obtain ⟨e1, own1, -, hv⟩ := zqReadUx hl hX hown hAW hS hownc hb
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDe, hDc, hDs, hBs, hDv, XB, hDX, hBX, hBown⟩ := uuDigMove (n := n) (l' := l') hl hX hSh
    (uxShG_B hl hX hS (hMv n l l' _ _ hl hX hl' hX')) hownc hb hDW IH
  rw [hBW] at hBown hBs
  have hXs' : X = 0 ∨ ∃ Xh, UjSh S l (Om ω) X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, uuShG S l' Eb Th (uuOw S) (Om ω) XB Xh := Rw.rwOwn_sh hBown
  have hXBs' : XB = 0 ∨ ∃ Xh, UjSh S l' (Om ω) XB Xh := by
    rcases hXBs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh' _ _ _ h).1⟩
  have hec := rwOwn_code hl hX hownc
  have heW := roGx_lt_Om2 hρ1 hec
  have heT : e < leTe S (X + Om (1 + 1)) (Om ω) := by
    refine (hb.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDX hBX
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hDW hDWW
  rw [hBW, hBWW] at hBaW
  have hXC : X ∈ S.CSet (Om ω + leWe (X + Om (1 + 1))) (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) := by
    rcases hXs' with rfl | ⟨Xh, hs'⟩
    · exact CSet.zero_mem _ _
    · exact ujMem hs' (ujX_le_base X _ (Om ω)) (rvWX_le le_rfl X _) le_rfl
  have hTown : Om ω + leWe (X + Om (1 + 1)) ∈ S.CSet (Om ω + leWe (X + Om (1 + 1)))
      (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (zjOmW_own _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTown
  rw [hBaW] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) (Om ω) := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) (Om ω) :=
    uuBase_lower hXBs' le_rfl (zjBaseX hAW' (zqX_WY hXBs')) le_rfl hBeT
  obtain ⟨e1', -, -, -⟩ := zqReadUx hl' hX' hown' hAW' hS' hBown hb'
  have hcown := uuOwn_own hl hX hSh hownc hb
  obtain ⟨hDa, hBa⟩ := mxB_atom (n := n) hDs hcown
  obtain ⟨hBH, hBA⟩ := uuOwn_mem hl' hX' hSh' hBown hb'
  have hvθ : v < ConjT.th S := hv.trans_le uxY2_le_th
  have hdθ := zjTh_add_le hvθ
  obtain ⟨hDθ, hBθ⟩ := ljB_th (S := S) (n := n)
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hDθ hDv
  have hownd : ConjT.Aη S (cdEta S l) + (ConjT.th S + v) ∈ S.CSet (ConjT.Aη S (cdEta S l) + (ConjT.th S + v))
      (S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1)) := by
    rw [← add_assoc]; exact own1
  have hbd : S.psi (ConjT.Aη S (cdEta S l) + (ConjT.th S + v)) (Om 1) < Bc.bcC S (n + 1) :=
    (Xs.xsLt_delta hl hX hdθ).trans hδr
  refine ⟨hDa, ?_, ?_, ?_, ?_⟩
  · rw [hBa, hBs]; exact ⟨_, hBH, hBA, rfl⟩
  · have h := (mvB_lt_iff (k := n) hDa hKB.1).2 hsK
    rwa [hKB.2] at h
  · rw [e1, add_assoc]; exact hbd
  · rw [hBa, hBs, e1', e1, add_assoc (ConjT.Aη S (cdEta S l)), hBψ _ hDd hownd hbd, hBd, hBθ, add_assoc]

/-- `W^{W^{Y₃}} = Y₃`. -/
theorem zqY_fix : leWe (leWe (ugY S)) = ugY S := by
  have hW := (Ua.uaWfix (gg_SC_eps (uqY_SC (S := S))) uqW_lt_Y).2
  rw [hW, hW]

/-- **`B_n ψ_{Ω₂}(Ω_ω + Y₃) = ψ_{Ω₂}(Ω_ω + Y₃)`.** -/
theorem zqB_Y {n : ℕ} : MvD S (S.psi (Om ω + ugY S) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om ω + ugY S) (Om (1 + 1))) = S.psi (Om ω + ugY S) (Om (1 + 1)) := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDY, hBY⟩ := Yy.yyY3_D (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDY
  have h3 : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω + ugY S := Ry.ryOm3_lt.trans_le le_self_add
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (CSet.add_mem (zjOmW_own _) (Vq.vqY3_mem h3))
  exact ⟨hDs, by rw [hBs, hBa, hBW, hBY]⟩

/-- **`Zj.ZjAtK S ψ_{Ω₂}(Ω_ω + Y₃)`**: every atom `θ < s < ψ_{Ω₂}(Ω_ω + Y₃)` moves once the codes below it move
(the level system `Uu.uuLSY` past `Γ₂` with its move `Ux.uxLSB_Y`). -/
theorem zqAtK_Y : ZjAtK S (S.psi (Om ω + ugY S) (Om (1 + 1))) := by
  intro n l l' hR h1 hr hl' hB s hs hθs hsK IH
  have hKE : S.psi (Om ω + ugY S) (Om (1 + 1)) ≤ S.psi (Om ω + leWe (leWe (ugY S))) (Om (1 + 1)) := by
    rw [zqY_fix]
  exact zqAtMoveUx (Eb := ugY S) (Th := ugTh S) (fun _ _ hl hX => uuLSY hl hX)
    (fun _ _ _ _ _ hl hX hl' hX' => uxLSB_Y hl hX hl' hX') hR h1 hr hl' hB hKE zqB_Y s hs hθs hsK
    (fun x hx hxs => by
      obtain ⟨b1, b2, -, b4, b5⟩ := IH x hx hxs
      exact ⟨b1, b2, b4, b5⟩)

end Googology.Trans.PoR.InaccPsi.R2.Zq
