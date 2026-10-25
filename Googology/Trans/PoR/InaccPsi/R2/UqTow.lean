import Googology.Trans.PoR.InaccPsi.R2.UqWin

/-!
# Member systems of the Veblen nodes in a window `(F_u, F_{u+1})` past `Γ₂`: the towers

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q`,
`F_u = φ(Ω₂, u)` with `Γ₂ ≤ u` (so `Γ₂ ≤ F_u`), `N = φ(a, y')`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

`Ua.uaMA_tow`, `Ua.uaMA_towW`, `Ua.uaMA_towV` past `Γ₂`: the φ law `Ug.ugVeb` in place of `Ua.uaVeb`, the level
codes and the own transfers `Uq.uqCl_NWin`, `Uq.uqCl_levW`.

* `uqThCode` (`T a = Θ a` for a code `a < Ω₂`), `uqMA_tow` (**a tower dominating a normal fixed point gives countable
  members**, image `T`, bound `Y₃`);
* `uqMA_towW` (**`φ(1, y' + 1)` in a window past `Γ₂`: the tower `W^·` above `N + 1`**), `uqMA_towV`
  (**`φ(a' + 1, y' + 1)` in a window past `Γ₂`: the tower `φ(a', ·)` above `N + 1`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T a = Θ a` for `a < Ω₂`. -/
theorem uqThCode {a : Ordinal.{0}} (haW : a < Om (1 + 1)) : ugTh S l a = gxTh (upsilon l) (ldAtR S l) a := by
  rw [ugTh_lt (haW.trans uaGam_spec.2), uaThCode hl hX haW]

/-- **A tower dominating a normal fixed point gives countable members** (image `T`, bound `Y₃`). -/
theorem uqMA_tow {E N : Ordinal.{0}} (f g fh gh : Ordinal.{0} → Ordinal.{0})
    (hEY : E < ugY S) (hNH : N ∈ cdHull S l) (hNE : N + 1 < E)
    (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x) (hE : E = nfp f (N + 1))
    (hfhm : Monotone fh) (hfgh : ∀ x, fh x ≤ gh x) (hEh : ugTh S l E = nfp fh (ugTh S l N + 1))
    (hg : ∀ x, x ∈ cdHull S l → N < x → x < E → g x ∈ cdHull S l ∧ g x < E ∧ x ≤ g x)
    (hTg : ∀ x, x ∈ cdHull S l → N < x → x < E → ugTh S l (g x) = gh (ugTh S l x))
    (hcN : ∀ Q, SC Q → ∀ h, UgC S (1 + 1) Q h → N < h → h ≤ E → UgC S (1 + 1) Q N)
    (hcg : ∀ Q, SC Q → ∀ x h, UgC S (1 + 1) Q h → N < x → g x ≤ h → h ≤ E →
      UgC S (1 + 1) Q x → UgC S (1 + 1) Q (g x)) :
    UqMA S l E := by
  set u := txTw g (N + 1) with hu_def
  have hus : ∀ j, u (j + 1) = g (u j) := fun j => rfl
  have hu : ∀ j, u j ∈ cdHull S l ∧ u j < E ∧ N < u j := by
    intro j
    induction j with
    | zero => exact ⟨CSet.succ_mem hNH, hNE, lt_add_one N⟩
    | succ j ih =>
      obtain ⟨a1, a2, a3⟩ := hg (u j) ih.1 ih.2.2 ih.2.1
      rw [hus]
      exact ⟨a1, a2, ih.2.2.trans_le a3⟩
  have hstep : ∀ j, u j ≤ u (j + 1) := fun j => by
    rw [hus]; exact (hg (u j) (hu j).1 (hu j).2.2 (hu j).2.1).2.2
  have hmono : Monotone u := monotone_nat_of_le_succ hstep
  have hNY : N + 1 < ugY S := hNE.trans hEY
  refine ⟨fun m => ∃ j, m = u (j + 1), ?_, ⟨_, 0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨j, rfl⟩
    obtain ⟨a1, a2, a3⟩ := hu (j + 1)
    exact ⟨a1, Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le a3), a2⟩
  · intro y _ hy
    rw [hE] at hy
    obtain ⟨j, hj⟩ := taTw_cof hfm hfg hy u le_rfl hus
    exact ⟨_, ⟨j, rfl⟩, hj.trans_le (hstep j)⟩
  · intro w hw
    rw [hEh] at hw
    have hu0 : ugTh S l N + 1 ≤ ugTh S l (u 0) := (ugSucc hl hX hNH hNY).symm.le
    obtain ⟨j, hj⟩ := taTw_cof hfhm hfgh hw (fun j => ugTh S l (u j)) hu0
      (fun j => by
        show ugTh S l (u (j + 1)) = gh (ugTh S l (u j))
        rw [hus]; exact hTg _ (hu j).1 (hu j).2.2 (hu j).2.1)
    refine ⟨_, ⟨j, rfl⟩, hj.trans_le ?_⟩
    exact ugLe hl hX (hu j).1 (hu (j + 1)).1 ((hu (j + 1)).2.1.trans hEY) (hstep j)
  · rintro Q hQ m h ⟨j, rfl⟩ h1 h2 hh
    have hNc : UgC S (1 + 1) Q N := hcN Q hQ h hh ((hu (j + 1)).2.2.trans_le h1) h2
    have key : ∀ i, i ≤ j + 1 → UgC S (1 + 1) Q (u i) := by
      intro i
      induction i with
      | zero => intro _; exact UgC.add hNc (UgC.small (gg_one_lt_of_SC hQ))
      | succ i ih =>
        intro hi
        have hle : u (i + 1) ≤ h := (hmono hi).trans h1
        rw [hus] at hle ⊢
        exact hcg Q hQ (u i) h hh (hu i).2.2 hle h2 (ih (Nat.le_of_succ_le hi))
    exact key (j + 1) le_rfl

/-- **`φ(1, y' + 1)` in a window past `Γ₂` has countable members**: the tower `W^·`. -/
theorem uqMA_towW {u y' : Ordinal.{0}} (hGu : uaGam ≤ u) (hy'H : y' ∈ cdHull S l)
    (hFN : veblen (Om (1 + 1)) u ≤ veblen 1 y') (hEX : veblen 1 (y' + 1) < veblen (Om (1 + 1)) (u + 1))
    (hEY : veblen 1 (y' + 1) < ugY S) : UqMA S l (veblen 1 (y' + 1)) := by
  have hGN : uaGam ≤ veblen 1 y' := (uqGam_le_F hGu).trans hFN
  set E := veblen 1 (y' + 1) with hE_def
  set N := veblen 1 y' with hN_def
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := CSet.one_mem _ _
  have hNH : N ∈ cdHull S l := CSet.phi_mem h1H hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim one_ne_zero
  have hEfix : ω ^ E = E := gg_veblen_eps one_ne_zero
  have hGE : uaGam ≤ E := hGN.trans hNE.le
  have hΩE : Om (1 + 1) < E := uaGam_spec.2.trans_le hGE
  have hT1 : ugTh S l 1 = 1 := by rw [uqThCode hl hX hW1, sqTh_one hl hX]
  have hy'1Y : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hTE : ugTh S l E = veblen 1 (ugTh S l y' + 1) := by
    rw [ugVeb hl hX h1H (CSet.succ_mem hy'H) one_ne_zero hGE hEY, hT1, ugSucc hl hX hy'H hy'1Y]
  have hTN : ugTh S l N = veblen 1 (ugTh S l y') := by
    rw [ugVeb hl hX h1H hy'H one_ne_zero hGN (hNE.trans hEY), hT1]
  refine uqMA_tow hl hX (veblen 0) leWe (veblen 0) leOe hEY hNH (hElim.add_one_lt hNE)
    (veblen_right_strictMono 0).monotone ?_ ?_ (veblen_right_strictMono 0).monotone ?_ ?_ ?_ ?_ ?_ ?_
  · intro x; rw [veblen_zero_apply]; unfold leWe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x ldOm2_SC.1)
  · have h := taVeb_succ 0 y'
    rw [zero_add] at h
    exact h
  · intro x; rw [veblen_zero_apply]; unfold leOe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x (Om_pos one_ne_zero))
  · have h := taVeb_succ 0 (ugTh S l y')
    rw [zero_add] at h
    rw [hTE, hTN, h]
  · intro x hxH _ hxE
    refine ⟨leWe_mem hxH, ?_, tnLe_We x⟩
    unfold leWe; conv_rhs => rw [← hEfix]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix hEfix hΩE hxE)
  · intro x hxH _ hxE
    have hWE : leWe x < E := by
      unfold leWe; conv_rhs => rw [← hEfix]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix hEfix hΩE hxE)
    have h := ugAddW hl hX (CSet.zero_mem _ _) hxH (dvd_zero _) (by rw [zero_add]; exact hWE.trans hEY)
    rwa [zero_add, ugTh_zero, zero_add] at h
  · intro Q hQ h hh h1 h2
    exact uqCl_NWin hQ hW1 hFN hh h1 h2 (h2.trans_lt hEX)
  · intro Q hQ x h _ _ _ _ hx
    exact uqWe hQ hx

/-- **`φ(a' + 1, y' + 1)` (`1 ≤ a'`, `a' + 1 < Ω₂`) in a window past `Γ₂` has countable members**: the tower
`φ(a', ·)` above `N + 1`. -/
theorem uqMA_towV {u a' y' : Ordinal.{0}} (hGu : uaGam ≤ u) (ha'H : a' ∈ cdHull S l) (ha'1 : 1 ≤ a')
    (haW : a' + 1 < Om (1 + 1)) (hy'H : y' ∈ cdHull S l) (hFN : veblen (Om (1 + 1)) u ≤ veblen (a' + 1) y')
    (hEX : veblen (a' + 1) (y' + 1) < veblen (Om (1 + 1)) (u + 1)) (hEY : veblen (a' + 1) (y' + 1) < ugY S) :
    UqMA S l (veblen (a' + 1) (y' + 1)) := by
  have hGN : uaGam ≤ veblen (a' + 1) y' := (uqGam_le_F hGu).trans hFN
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set E := veblen (a' + 1) (y' + 1) with hE_def
  set N := veblen (a' + 1) y' with hN_def
  have ha'W : a' < Om (1 + 1) := (lt_add_one a').trans haW
  have haH : a' + 1 ∈ cdHull S l := CSet.succ_mem ha'H
  have ha'c : GxCl (upsilon l) (ldAtR S l) a' := (ldHull_iff hl hX ha'W).1 ha'H
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have ha'0 : a' ≠ 0 := (zero_lt_one.trans_le ha'1).ne'
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have hGE : uaGam ≤ E := hGN.trans hNE.le
  have hy'1Y : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hΘa : ugTh S l (a' + 1) = gxTh (upsilon l) (ldAtR S l) a' + 1 := by
    rw [uqThCode hl hX haW, gxTh_add hρSC hAt ha'c, sqTh_one hl hX]
  have hTE : ugTh S l E = veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (ugTh S l y' + 1) := by
    rw [ugVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEY, hΘa, ugSucc hl hX hy'H hy'1Y]
  have hTN : ugTh S l N = veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (ugTh S l y') := by
    rw [ugVeb hl hX haH hy'H ha0 hGN (hNE.trans hEY), hΘa]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  refine uqMA_tow hl hX (veblen a') (veblen a') (veblen (gxTh (upsilon l) (ldAtR S l) a'))
    (veblen (gxTh (upsilon l) (ldAtR S l) a')) hEY hNH (hElim.add_one_lt hNE)
    (veblen_right_strictMono a').monotone (fun x => le_rfl) (taVeb_succ a' _)
    (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, hTN, taVeb_succ]
  · intro x hxH _ hxE
    refine ⟨CSet.phi_mem ha'H hxH, ?_, right_le_veblen _ _⟩
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hxE
      _ = E := hfix
  · intro x hxH hNx hxE
    have hvG : uaGam ≤ veblen a' x := (hGN.trans hNx.le).trans (right_le_veblen _ _)
    have hlt : veblen a' x < E := by
      calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hxE
        _ = E := hfix
    rw [ugVeb hl hX ha'H hxH ha'0 hvG (hlt.trans hEY), uqThCode hl hX ha'W]
  · intro Q hQ h hh h1 h2
    exact uqCl_NWin hQ haW hFN hh h1 h2 (h2.trans_lt hEX)
  · intro Q hQ x h hh hNx hgx h2 hx
    have hFx : veblen (Om (1 + 1)) u < veblen a' x := (hFN.trans_lt hNx).trans_le (right_le_veblen _ _)
    have ha'c' := uqCl_levW hQ ha'W hFx h hh hgx (h2.trans_lt hEX)
    exact UgC.phi ha'c' hx

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
