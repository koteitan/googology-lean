import Googology.Trans.PoR.InaccPsi.R2.ZjRw
import Googology.Trans.PoR.InaccPsi.R2.UdRoad
import Googology.Trans.PoR.InaccPsi.R2.UgRead

/-!
# Level systems over the base `Ω_ω`: the atoms below `ψ_{Ω₂}(Ω_ω + W^{W^{E_b}})` move

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`,
`W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)` (`Le.leTe`), a level system `St.StLS S λ E_b Th` with its move
`St.StLSB`, the family `St.stShG S λ E_b Th` (shifts own relative to a base).

The base-`0` statement `St.stRepG` asks the closure condition `Sn.SnCL S E 0 0` of the level `E` read off the
atom argument `d`; over the base `Ω_ω` the atom is `ψ_{Ω₂}(Ω_ω + d')` and the closure condition
`Sn.SnCL S E Ω_ω 0` of the level read off the DIGIT PART `d'` follows from `Sn.snExtrRem` (the digit part of a
normal-form argument is a code: `W^{W^{E_b}} ∣ Ω_ω`).  So every level system gives its atoms over `Ω_ω`.

* `zqRepSt` (**every atom `θ < s < T_{W^{E_b}}(Ω_ω)` is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)` own over `Ω_ω`**);
* `zqReadSt` (**`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`**);
* `zqB_Te` (`B_n T_{W^{E}}(Ω_ω) = T_{W^{E}}(Ω_ω)` when `B_n E = E`);
* `zqAtMoveSt` (**every atom `θ < s < T_{W^{E_b}}(Ω_ω)` moves** once the codes below it move, for every level
  system at every restart index with its move);
* `zqAtMoveUd` / `zqAtK_Gam` (**`Zj.ZjAtK S ψ_{Ω₂}(Ω_ω + Γ₂)`**, `Γ₂ = ψ_{Ω₃}(0)`, from the systems `Ud.udLSX k`).

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
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Zj

variable {S : InaccSeq.{0}} {Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}}

/-- `W^{W^E} < Ω_ω` for `E < ψ_{Ω₃}(0)`. -/
theorem zqWW_lt {E : Ordinal.{0}} (hE : E < S.psi 0 (Om (1 + 1 + 1))) : leWe (leWe E) < Om ω :=
  roWe_lt_OmW (roWe_lt_OmW (hE.trans stG3_lt_OmW))

/-- `W^E < ψ_{Ω₃}(0)` for `E < ψ_{Ω₃}(0)`. -/
theorem zqWe_lt_G3 {E : Ordinal.{0}} (hE : E < S.psi 0 (Om (1 + 1 + 1))) :
    leWe E < S.psi 0 (Om (1 + 1 + 1)) :=
  (leWe_lt_SC (rwG3_SC (S := S)) rwW_lt_G3 hE).1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l)) (hS : StLS S l Eb Th)

include hl hX hown hAW hS

/-- **Every atom `θ < s < T_{W^{E_b}}(Ω_ω)` of a level system is `ψ_{Ω₂}(Ω_ω + c)` with `(X, e, c, v)` own over
`Ω_ω`** (family `St.stShG S λ E_b Th`). -/
theorem zqRepSt (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hθs : ConjT.th S < s)
    (hsK : s < S.psi (Om ω + leWe (leWe Eb)) (Om (1 + 1))) :
    ∃ X e c v, (X = 0 ∨ ∃ Xh, stShG S l Eb Th (Om ω) X Xh) ∧
      RwOwn S l (stShG S l Eb Th) X e (Om ω) c v ∧ RoBaseE S l X e (Om ω) ∧
      s = S.psi (Om ω + c) (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hG3 := rwG3_SC (S := S)
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  obtain ⟨d, rfl, hnf, hdH, -⟩ := snNf hs hρ1.le
  -- `d = Ω_ω + d'`
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
  have hWWb := zqWW_lt (S := S) hS.ltG3
  have hd'ε : d' < leWe (leWe Eb) := by
    by_contra h
    push Not at h
    have h2 : Om ω + leWe (leWe Eb) ≤ d := by rw [hdd]; exact (add_le_add_iff_left _).2 h
    exact absurd hsK (not_lt.2 (psi_mono (S := S) hκ h2).1)
  rw [hdd] at hnf hdH hs ⊢
  have hKdvd : leWe (leWe Eb) ∣ Om ω := zjWX_dvd (roWe_lt_OmW (hS.ltG3.trans stG3_lt_OmW))
  have hKG : leWe Eb < S.psi 0 (Om (1 + 1 + 1)) := zqWe_lt_G3 hS.ltG3
  have hd'H : d' ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) := snHullRem hdH hKdvd hd'ε
  -- the level of the digit part
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
  have he1 : 1 ≤ E := le_add_self
  have hdW : d' < leWe (leWe E) := by
    refine (roLt_We_log d').trans_le (leWe_mono ?_)
    exact Order.add_one_le_of_lt (roLt_We_log Y)
  have hst : S.psi (Om ω + d') (Om (1 + 1)) < S.psi (Om ω + leWe (0 + leWe E)) (Om (1 + 1)) := by
    rw [zero_add]; exact psi_lt_psi hκ ((add_lt_add_iff_left _).2 hdW) hnf
  -- the closure condition at the base `Ω_ω`
  have hcl : SnCL S E (Om ω) 0 := by
    intro Q hQ hQ'
    have htQ := hst.le.trans hQ'
    have hdQ : LeCl (Om (1 + 1)) Q d' := snExtrRem hnf hKdvd hd'ε hKG hQ htQ
    exact LeCl.add (snLogW hQ (snLogW hQ hdQ)) (LeCl.small (gg_one_lt_of_SC hQ))
  have hEH : E ∈ cdHull S l :=
    CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem (ldDivK_mem ldOm2_SC (leLog_mem hd'H))))
  have hEW : 0 + leWe E < Om ω := by
    rw [zero_add]; exact roWe_lt_OmW (hE.trans (hS.ltG3.trans stG3_lt_OmW))
  have hb : RoBaseE S l (0 + leWe E) 0 (Om ω) := zjBaseX hAW hEW
  have hcls := stClsLev_all hl hX hS E hEH he1 hE (Om ω) 0 0 (Or.inl ⟨rfl, rfl⟩) hcl (Om ω) le_rfl hb
    (zjRd hl hX hown hAW)
  have htT : S.psi (Om ω + d') (Om (1 + 1)) < leTe S (0 + leWe E + 0) (Om ω) := by
    rw [add_zero]; exact hst
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hownc, hbo, e1⟩
  · rw [hdd] at hθs; exact absurd hθs (not_lt.2 h)
  · exact ⟨X', e', c, v, rwOwn_sh hownc, hownc, hbo, e1⟩

/-- **`Θ(ψ_{Ω₂}(Ω_ω + c)) = ψ_{Ω₁}(A + θ + v)`** for every own `(X, e, c, v)` over `Ω_ω` of a level system. -/
theorem zqReadSt {X e c v : Ordinal.{0}} (hownc : RwOwn S l (stShG S l Eb Th) X e (Om ω) c v)
    (hb : RoBaseE S l X e (Om ω)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1) ∧
      ConjT.Aη S (cdEta S l) + ConjT.th S + v ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + v)
        (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + v) (Om 1)) ∧ c < leWe (X + e) ∧
      v < S.psi 0 (Om (1 + 1)) :=
  rwOwnRead hl hX (stShG_sh hl hX hS) hownc _ hb (zjHat hl hX hown hAW) (zjBase0 hl hX hown hAW)

end Main

/-- `ω^X = X`, `W^X = X`, `W^{W^X} = X` for the levels `X = Ud.udX k` (Veblen values above `Ω₂`). -/
theorem zqX_fix (k : ℕ) : ω ^ Ud.udX k = Ud.udX k ∧ leWe (leWe (Ud.udX k)) = Ud.udX k := by
  have hE : ω ^ Ud.udX k = Ud.udX k := by
    rw [Ud.udX_eq]
    have hpos : (0 : Ordinal.{0}) < (fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1) := by
      induction k with
      | zero => exact lt_of_lt_of_le ldOm2_SC.1 le_self_add
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact lt_of_lt_of_le ih (left_le_veblen _ _)
    have h := veblen_veblen_of_lt hpos (0 : Ordinal.{0})
    rwa [veblen_zero_apply] at h
  have hW := (Ua.uaWfix hE (Ud.udX_gt k)).2
  exact ⟨hE, by rw [hW, hW]⟩

/-- **`B_n ψ_{Ω₂}(Ω_ω + X_k) = ψ_{Ω₂}(Ω_ω + X_k)`** (`X_k = Ud.udX k`). -/
theorem zqB_X {n : ℕ} (k : ℕ) : MvD S (S.psi (Om ω + Ud.udX k) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (Om ω + Ud.udX k) (Om (1 + 1))) = S.psi (Om ω + Ud.udX k) (Om (1 + 1)) := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDX, hBX⟩ := Ud.udX_B (S := S) (n := n) k
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDX
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (CSet.add_mem (zjOmW_own _) (Ug.ugX_mem _ _ k))
  exact ⟨hDs, by rw [hBs, hBa, hBW, hBX]⟩

/-- **Every atom `θ < s < K` moves** once the codes below it move, for a level system `St.StLS` at every restart
index with its move `St.StLSB`, and a bound `K ≤ T_{W^{E_b}}(Ω_ω)` fixed by `B_n`. -/
theorem zqAtMoveSt
    (hSys : ∀ l ηx, IsRestartIdx l → upsilon l < Pv S ηx → StLS S l Eb Th)
    (hMv : ∀ n l l' ηx ηx', IsRestartIdx l → upsilon l < Pv S ηx → IsRestartIdx l' → upsilon l' < Pv S ηx' →
      StLSB S n l l' Eb Th)
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
  have hSh := stShG_sh hl hX hS
  have hSh' := stShG_sh hl' hX' hS'
  rcases zqRepSt hl hX hown hAW hS s hs hθs (hsK.trans_le hKE) with ⟨X, e, c, v, hXs, hownc, hb, rfl⟩
  obtain ⟨e1, own1, -, hv⟩ := zqReadSt hl hX hown hAW hS hownc hb
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDe, hDc, hDs, hBs, hDv, XB, hDX, hBX, hBown⟩ := rwDigMove (n := n) (l' := l') hl hX hSh
    (stShG_B hl hX hl' hX' hS hS' (hMv n l l' _ _ hl hX hl' hX')) hownc hb hDW IH
  rw [hBW] at hBown hBs
  have hXs' : X = 0 ∨ ∃ Xh, RvSh S l (Om ω) X Xh := by
    rcases hXs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh _ _ _ h).1⟩
  have hXBs : XB = 0 ∨ ∃ Xh, stShG S l' Eb Th (Om ω) XB Xh := rwOwn_sh hBown
  have hXBs' : XB = 0 ∨ ∃ Xh, RvSh S l' (Om ω) XB Xh := by
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
    · exact rvMem hs' (rvWX_le le_rfl X _) le_rfl
  have hTown : Om ω + leWe (X + Om (1 + 1)) ∈ S.CSet (Om ω + leWe (X + Om (1 + 1)))
      (S.psi (Om ω + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (zjOmW_own _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTown
  rw [hBaW] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) (Om ω) := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) (Om ω) :=
    rwBase_lower hXBs' le_rfl (zjBaseX hAW' (zjX_W hXBs')) le_rfl hBeT
  obtain ⟨e1', -, -, -⟩ := zqReadSt hl' hX' hown' hAW' hS' hBown hb'
  have hcown := rwOwn_own hl hX hSh hownc hb
  obtain ⟨hDa, hBa⟩ := mxB_atom (n := n) hDs hcown
  obtain ⟨hBH, hBA⟩ := rwOwn_mem hl' hX' hSh' hBown hb'
  have hvθ : v < ConjT.th S := hv.trans_le rnG_le_th
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

/-- `ψ_{Ω₂}(Ω_ω + ·)` is continuous at `Γ₂`: an `s < ψ_{Ω₂}(Ω_ω + Γ₂)` is below `ψ_{Ω₂}(Ω_ω + X_k)` for some `k`. -/
theorem zqPsi_Gam {s : Ordinal.{0}} (hs : s < S.psi (Om ω + Ua.uaGam) (Om (1 + 1))) :
    ∃ k, s < S.psi (Om ω + Ud.udX k) (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hlim : IsSuccLimit (Om ω + Ua.uaGam) := isSuccLimit_add _ Ua.uaGam_spec.1.isSuccLimit
  rw [Lw.lw_psi_limit S hκ hlim] at hs
  have hbdd : BddAbove (range fun e : Iio (Om ω + Ua.uaGam) => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
  haveI : Nonempty (Iio (Om ω + Ua.uaGam)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨⟨e, he⟩, hse⟩ := (lt_ciSup_iff hbdd).1 hs
  rcases lt_or_ge e (Om ω) with heW | heW
  · refine ⟨0, hse.trans_le (psi_mono hκ ?_).1⟩
    exact heW.le.trans le_self_add
  · have hee : e = Om ω + (e - Om ω) := (Ordinal.add_sub_cancel_of_le heW).symm
    set e' := e - Om ω
    have hse' : s < S.psi (Om ω + e') (Om (1 + 1)) := by rw [← hee]; exact hse
    have he' : e' < Ua.uaGam := (add_lt_add_iff_left _).1 (by rw [← hee]; exact he)
    obtain ⟨k, hk⟩ := Ud.udX_cof he'
    exact ⟨k, hse'.trans_le (psi_mono hκ ((add_le_add_iff_left _).2 hk.le)).1⟩

/-- **`Zj.ZjAtK S ψ_{Ω₂}(Ω_ω + Γ₂)`**: every atom `θ < s < ψ_{Ω₂}(Ω_ω + Γ₂)` moves once the codes below it move
(`Γ₂ = ψ_{Ω₃}(0)`; the level systems `Ud.udLSX k` with their moves `Ud.udLSBX k`). -/
theorem zqAtK_Gam : ZjAtK S (S.psi (Om ω + Ua.uaGam) (Om (1 + 1))) := by
  intro n l l' hR h1 hr hl' hB s hs hθs hsK IH
  obtain ⟨k, hk⟩ := zqPsi_Gam hsK
  have hKE : S.psi (Om ω + Ud.udX k) (Om (1 + 1)) ≤ S.psi (Om ω + leWe (leWe (Ud.udX k))) (Om (1 + 1)) := by
    rw [(zqX_fix k).2]
  obtain ⟨a1, a2, a3, a4, a5⟩ := zqAtMoveSt (fun _ _ hl hX => Ud.udLSX hl hX k)
    (fun _ _ _ _ _ hl hX hl' hX' => Ud.udLSBX hl hX hl' hX' k) hR h1 hr hl' hB hKE (zqB_X k) s hs hθs hk
    (fun x hx hxs => by
      obtain ⟨b1, b2, -, b4, b5⟩ := IH x hx hxs
      exact ⟨b1, b2, b4, b5⟩)
  refine ⟨a1, a2, a3.trans_le ?_, a4, a5⟩
  refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left _).2 ?_)).1
  exact (Ud.udX_lt k).le

end Googology.Trans.PoR.InaccPsi.R2.Zq
