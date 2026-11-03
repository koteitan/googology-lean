import Googology.Trans.PoR.InaccPsi.R2.YtLe
import Googology.Trans.PoR.InaccPsi.R2.UxRoad

/-!
# Every offset below `Y₃` above a base `a` with `Y₃ ∣ a`: the classification and the moves

`Y₃ = ψ_{Ω₃}(Ω₃)` (`Ug.ugY`), `W^E = Ω₂^E`, `Sh = Uu.uuShG S λ Y₃ (Ug.ugTh S) Uu.uuOw` (the shift family of the level
system `Uu.uuLSY`, at every base), `Rw.RwOwn` the own arguments over a base.  This is `Ux.uxRepG` / `Ux.uxAtMoveG`
(base `0`, image `A + 1`) at a base `a` with `Y₃ ∣ a` and image `Â = A + D` (a `Yj.YjBase`); every other ingredient
(`Ux.uxClsLev_all`, `Uu.uuOwnRead`, `Uu.uuDigMove`, `Ux.uxShG_B`, `Uu.uuOwn_own`, `Uu.uuOwn_mem`) is already
generic in the base.

* `ytWe_dvd_Y` (`W^x ∣ Y₃` for `x < Y₃`), `ytY_dvd_We` (`Y₃ ∣ W^{Ω_{k+3}+e}`);
* `ytRepU` (**every atom `ψ₂(a) ≤ s < ψ₂(a + W^{W^{Y₃}})` is `ψ₂(a)` or `ψ₂(a + c)` with `c` own over `a`**
  (`Rw.RwOwn` of the family `Sh` with `Ro.RoBaseE` at `a`));
* `ytUxMove` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃)` MOVES** at a window, given `Yj.YjBase λ λ' A' a D`, `Y₃ ∣ a`,
  `Y₃ ∣ B_n a` and the moves of the codes below `s`);
* `ytTopMoveY` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Y₃)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the
  premise of WallBelow at `s`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq
  Googology.Trans.PoR.InaccPsi.R2.Uu Googology.Trans.PoR.InaccPsi.R2.Ux
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- `W^x ∣ Y₃` for `x < Y₃`. -/
theorem ytWe_dvd_Y {x : Ordinal.{0}} (hx : x < ugY S) : leWe x ∣ ugY S := by
  unfold leWe
  conv_rhs => rw [← gg_SC_eps (uqY_SC (S := S))]
  exact opow_dvd_opow ω (ldMul_lt_SC uqY_SC uqW_lt_Y hx).le

/-- `Y₃ ∣ W^{Ω_{k+3}+e}`. -/
theorem ytY_dvd_We (k : ℕ) (e : Ordinal.{0}) : ugY S ∣ leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) := by
  unfold leWe
  conv_lhs => rw [← gg_SC_eps (uqY_SC (S := S))]
  refine opow_dvd_opow ω ?_
  exact (ugY_lt_Om3.le.trans (ytOm3_le_X k)).trans (le_self_add.trans (Ordinal.le_mul_right _ ldOm2_SC.1))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every atom `ψ₂(a) ≤ s < ψ₂(a + W^{W^{Y₃}})` is `ψ₂(a)` or `ψ₂(a + c)` with `c` own over `a`.** -/
theorem ytRepU {a : Ordinal.{0}}
    (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
    (hY : ugY S ∣ a) (haH : a ∈ cdHull S l) (haW : a < Om ω) (hRd : RwRd S l a)
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hsa : S.psi a (Om (1 + 1)) ≤ s)
    (hsε : s < S.psi (a + leWe (leWe (ugY S))) (Om (1 + 1))) :
    s = S.psi a (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, uuShG S l (ugY S) (ugTh S) (uuOw S) a X Xh) ∧
      RwOwn S l (uuShG S l (ugY S) (ugTh S) (uuOw S)) X e a c v ∧ RoBaseE S l X e a ∧
        s = S.psi (a + c) (Om (1 + 1)) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hS := uuLSY (S := S) hl hX
  have hYSC := uqY_SC (S := S)
  have hWY := uqW_lt_Y (S := S)
  obtain ⟨d, rfl, hnf, hdH, hdA⟩ := snNf hs hρ1.le
  rcases lt_or_ge d a with hda | hda
  · exact Or.inl (le_antisymm (psi_mono (S := S) (InR_Om_succ 1) hda.le).1 hsa)
  obtain ⟨d', rfl⟩ := exists_add_of_le hda
  have hdε : d' < leWe (leWe (ugY S)) := by
    by_contra h
    push Not at h
    exact absurd hsε (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 h)).1)
  rcases eq_or_ne d' 0 with rfl | hd0
  · exact Or.inl (by rw [add_zero])
  obtain ⟨r, hr⟩ := hY
  have hmodY : ∀ {x : Ordinal.{0}}, x < ugY S → (a + x) % ugY S = x := fun hx => by
    rw [hr, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]
  set Y := log ω d' / Om (1 + 1) with hY_def
  set E := log ω Y / Om (1 + 1) + 1 with hE_def
  have hYlt : Y < leWe (ugY S) := by
    have h1 : leWe 0 ≤ d' := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hd0
    exact (sjLogW h1 hdε).2
  have hlY : log ω Y / Om (1 + 1) < ugY S := by
    rcases eq_or_ne Y 0 with h0 | hY0
    · rw [h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hS.lim.ne_bot
    · have h1 : leWe 0 ≤ Y := by rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 hY0
      exact (sjLogW h1 hYlt).2
  have hE : E < ugY S := hS.lim.succ_lt hlY
  have he1 : 1 ≤ E := le_add_self
  have hdW : d' < leWe (leWe E) := by
    refine (roLt_We_log d').trans_le (leWe_mono ?_)
    exact Order.add_one_le_of_lt (roLt_We_log Y)
  have hWE : leWe E < ugY S := (leWe_lt_SC hYSC hWY hE).1
  have hdY : d' < ugY S := hdW.trans (leWe_lt_SC hYSC hWY hWE).1
  have hst : S.psi (a + d') (Om (1 + 1)) < S.psi (a + leWe (0 + leWe E)) (Om (1 + 1)) := by
    rw [zero_add]; exact psi_lt_psi (InR_Om_succ 1) ((add_lt_add_iff_left a).2 hdW) hnf
  have hcl3 : UgCL S E a 0 := by
    intro Q hQ hQ'
    have htQ := hst.le.trans hQ'
    have hmem : d' ∈ S.CSet (a + d') Q := by
      have h := ldModK_mem (S := S) (κ := ugY S) hYSC (CSet_mono le_rfl htQ hnf)
      rwa [hmodY hdY] at h
    have hdQ : UgC S (1 + 1) Q d' := uqC_mem hQ htQ hmem hdY
    exact UgC.add (uxLogW hQ (uxLogW hQ hdQ)) (UgC.small (gg_one_lt_of_SC hQ))
  have hWWa : leWe (0 + leWe (Om (1 + 1))) ∣ a := by
    rw [zero_add, hr]; exact (ytWe_dvd_Y (leWe_lt_SC hYSC hWY hWY).1).trans (dvd_mul_right _ _)
  have hcl : uuOw S E a 0 := by
    rcases lt_or_ge E (Om (1 + 1)) with hEW | hEW
    · refine Or.inl ⟨hEW, ?_⟩
      have hTE : E < S.psi (a + leWe (0 + leWe E)) (Om (1 + 1)) :=
        uxCode_lt (SC_psi (InR_Om_succ 1) _) (hcl3 _ (SC_psi (InR_Om_succ 1) _) le_rfl) hEW
      exact uxEX_own (fun d _ => ytOwnAll hown d) (CSet.zero_mem _ _) hWWa
        (fun Q hQ _ => UgC.zero hQ.1) (by rw [zero_add]; exact (leWe_lt_SC hYSC hWY hWY).1) hEW hTE
    · exact Or.inr ⟨hEW, hcl3⟩
  have hd'H : d' ∈ cdHull S l := by
    have h := ldModK_mem (S := S) (κ := ugY S) hYSC hdH
    rwa [hmodY hdY] at h
  have hEH : E ∈ cdHull S l :=
    CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem (ldDivK_mem ldOm2_SC (leLog_mem hd'H))))
  have hEW : E < Om ω := hE.trans (ugY_lt_Om3.trans Ry.ryOm3_lt)
  have hb : RoBaseE S l (0 + leWe E) 0 a := by
    refine ⟨?_, haH, ?_, fun d _ => ytOwnAll hown d, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero, hr]; exact (ytWe_dvd_Y hWE).trans (dvd_mul_right _ _)
    · rw [zero_add, add_zero]
      exact (vkOmW.1.isPrincipal haW (roWe_lt_OmW (roWe_lt_OmW hEW))).trans_le (ConjT.OmW_le_A S _)
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hcls := uxClsLev_all hl hX hS E hEH he1 hE a 0 0 (Or.inl ⟨rfl, rfl⟩) hcl a le_rfl hb hRd
  have htT : S.psi (a + d') (Om (1 + 1)) < leTe S (0 + leWe E + 0) a := by rw [add_zero]; exact hst
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hownc, hbo, e1⟩
  · exact Or.inl (le_antisymm h hsa)
  · exact Or.inr ⟨X', e', c, v, rwOwn_sh hownc, hownc, hbo, e1⟩

end Main

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃)` MOVES** above a base with a law at both ends with `Y₃ ∣ a`, `Y₃ ∣ B_n a`. -/
theorem ytUxMove {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hY : ugY S ∣ a)
    (hY' : ugY S ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsY : s < S.psi (a + ugY S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have hS := uuLSY (S := S) hl hX
  have hS' := uuLSY (S := S) hl' hX'
  have hSh := uuShG_sh hl hX hS
  have hSh' := uuShG_sh hl' hX' hS'
  have hRd : RwRd S l a := ⟨A + D, hb.hat, hb.law⟩
  have hsε : s < S.psi (a + leWe (leWe (ugY S))) (Om (1 + 1)) :=
    hsY.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2 uxY_le_WW)).1
  rcases ytRepU hl hX hb.own hY hb.D_a.1 hb.D_a.2.2 hRd s hs hsa hsε with rfl | ⟨X, e, c, v, hXs, hownc, hbe, rfl⟩
  · obtain ⟨hD, -, hat, hmv⟩ := yjBlkMove hR h1 hr hl' hB hA' hρ' (a := a) (D := D) hb
      (GxCl.zero (mvUps_pos hl)) ((Om_pos one_ne_zero).trans (ldOm1_lt_Top _))
      (fun x hx hxs => IH x hx (by rwa [add_zero] at hxs))
    rw [add_zero] at hD hat hmv
    exact ⟨hD, hat, hmv⟩
  obtain ⟨hth, hownv, -, hv⟩ := uuOwnRead hl hX hSh hownc (A + D) hbe hb.hat hb.law
  obtain ⟨hDe, hDc, hDac, hBac, hDv, XB, hDXB, hBXB, hown'⟩ := uuDigMove (n := n) (l' := l') hl hX hSh
    (uxShG_B hl hX hS (uxLSB_Y hl hX hl' hX')) hownc hbe hb.mv_a (fun x hx hxs => by
      obtain ⟨a1, b1, -, d1, e1⟩ := IH x hx hxs
      exact ⟨a1, b1, d1, e1⟩)
  have hXBs : XB = 0 ∨ ∃ Xh, uuShG S l' (ugY S) (ugTh S) (uuOw S) (Bc.bcB S n a) XB Xh := rwOwn_sh hown'
  -- the base `B_n a` of exponent `B_n e` at `λ'`
  have hec := rwOwn_code hl hX hownc
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have heW := roGx_lt_Om2 hρ1 hec
  have hXY : X + Om (1 + 1) < ugY S := by
    rcases hXs with rfl | ⟨Xh, h⟩
    · rw [zero_add]; exact uqW_lt_Y
    · exact ((hSh _ _ _ h).1).ltY
  have heT : e < leTe S (X + Om (1 + 1)) a := by
    refine (hbe.2.2.2.2 e hec le_rfl).trans_le ?_
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left a).2
      (leWe_mono ((add_le_add_iff_left X).2 heW.le)))).1
  obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDXB hBXB
  have hXC : X ∈ S.CSet (a + leWe (X + Om (1 + 1))) (S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1))) := by
    rcases hXs with rfl | ⟨Xh, hs'⟩
    · exact CSet.zero_mem _ _
    · exact ujMem (hSh _ _ _ hs').1 (ujX_le_base X _ a) (rvWX_le le_rfl X _) le_rfl
  have hTown : a + leWe (X + Om (1 + 1)) ∈ S.CSet (a + leWe (X + Om (1 + 1)))
      (S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem (ytOwnAll hb.own _) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _)))
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hb.mv_a hDWW
  rw [hBWW] at hBaW
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTown
  rw [hBaW] at hBT
  have hBeT : Bc.bcB S n e < leTe S (XB + Om (1 + 1)) (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDe hDT).2 heT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hXBs' : XB = 0 ∨ ∃ Xh, UjSh S l' (Bc.bcB S n a) XB Xh := by
    rcases hXBs with h0 | ⟨Xh, h⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Xh, (hSh' _ _ _ h).1⟩
  have hXBY : XB + Om (1 + 1) < ugY S := by
    rcases hXBs' with rfl | ⟨Xh, h⟩
    · rw [zero_add]; exact uqW_lt_Y
    · exact h.ltY
  have hb0' : RoBaseE S l' (XB + Om (1 + 1)) 0 (Bc.bcB S n a) := by
    obtain ⟨r', hr'⟩ := hY'
    refine ⟨?_, hb.D_a'.1, ?_, fun d _ => ytOwnAll hb.own' d, fun e' _ h' => ?_⟩
    · rw [add_zero, hr']
      exact (ytWe_dvd_Y hXBY).trans (dvd_mul_right _ _)
    · rw [add_zero]
      exact (vkOmW.1.isPrincipal hb.D_a'.2.2 (roWe_lt_OmW (hXBY.trans (ugY_lt_Om3.trans Ry.ryOm3_lt)))).trans_le
        (ConjT.OmW_le_A S _)
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hb' : RoBaseE S l' XB (Bc.bcB S n e) (Bc.bcB S n a) := uuBase_lower hXBs' le_rfl hb0' le_rfl hBeT
  obtain ⟨hth', -, -, -⟩ := uuOwnRead hl' hX' hSh' hown' (A' + Bc.bcB S n D) hb' hb.hat' hb.law'
  -- the move of the atom
  have hcown := uuOwn_own hl hX hSh hownc hbe
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDac hcown
  obtain ⟨hBH, hBA⟩ := uuOwn_mem hl' hX' hSh' hown' hb'
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hb.mv_D hDv
  have haYW : a + ugY S < Om ω := vkOmW.1.isPrincipal hb.D_a.2.2 (ugY_lt_Om3.trans Ry.ryOm3_lt)
  have hhi : S.psi (A + (D + v)) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← add_assoc, ← hth]; exact yjTh_hi hR h1 hr hl' hB (hsY.le.trans (yjPsi2_leW haYW))
  have hownd : A + (D + v) ∈ S.CSet (A + (D + v)) (S.psi (A + (D + v)) (Om 1)) := by
    rw [← add_assoc]; exact hownv
  have hψ := yjPsi1 hR h1 hr hl' hB hA' hρ' hDd hownd hhi
  refine ⟨hDs, ?_, ?_⟩
  · rw [hBs, hBac]; exact ⟨_, hBH, hBA, rfl⟩
  · rw [hBs, hBac, hth', hth, add_assoc A, hψ, hBd, add_assoc]

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Y₃)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the premise of
WallBelow at `s`. -/
theorem ytTopMoveY (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsY : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + ugY S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hd : ugY S ∣ β + leWe (X + e) := dvd_add ((ytY_dvd_We k e).trans hbe.1) (ytY_dvd_We k e)
  have hd' : ugY S ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]
    exact dvd_add ((ytY_dvd_We k _).trans hdv') (ytY_dvd_We k _)
  exact ytUxMove hR h1 hr hl' hB hA' hρ' hbt hd hd' hs hst hsY IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yt
