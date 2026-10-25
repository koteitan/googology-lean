import Googology.Trans.PoR.InaccPsi.R2.UaWin

/-!
# Member systems of the Veblen nodes inside a window `(φ(Ω₂, u), φ(Ω₂, u + 1))`: the towers

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`, `F_u = φ(Ω₂, u)` (windows `(F_u, F_{u+1})`, `u ≥ 1`), `N = φ(a, y')`, member systems
`Ua.UaMA`, `Ua.UaMB`.

* `uaLimT` (`T z` is a limit for a limit `z ∈ H_λ ∩ Γ₂`), `uaThCode` (`T a = Θ a` for a code `a < Ω₂`);
* `uaMA_tow` (**a tower dominating a normal fixed point gives countable members**, `Tx.txMA_tow` for `T`, the
  tower above `N + 1`);
* `uaMA_towW` (**`φ(1, y' + 1)` in a window: the tower `W^·` above `N + 1`**), `uaMA_towV` (**`φ(a' + 1, y' + 1)` in
  a window: the tower `φ(a', ·)` above `N + 1`**); the own transfer by `Ua.uaCl_NWin`, `Ua.uaCl_levW`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu
  Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T a = Θ a` for `a < Ω₂`. -/
theorem uaThCode {a : Ordinal.{0}} (haW : a < Om (1 + 1)) : uaTh S l a = gxTh (upsilon l) (ldAtR S l) a := by
  rw [uaTh_lt (haW.trans tgOm_lt_G)]; exact tuThL_code hl hX haW

/-- **`T z` is a limit for a limit `z ∈ H_λ ∩ Γ₂`.** -/
theorem uaLimT : ∀ z, z ∈ cdHull S l → IsSuccLimit z → z < uaGam → IsSuccLimit (uaTh S l z) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzH hlim hzG
  have h0 : 0 < z := hlim.bot_lt
  rcases lt_or_ge z (veblen (Om (1 + 1)) 1) with hzG' | hGz
  · rw [uaTh_lt hzG']; exact txLimT hl hX z hzH hlim hzG'
  by_cases hs : sgLW z < z
  · obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hzdec, hT, -⟩ := uaParts hl hX hzH h0 hzG
    set g := sgLW z with hg
    rw [hT]
    rcases eq_or_ne (z % leWe g) 0 with hr0 | hr0
    · rw [hr0, uaTh_zero, add_zero]
      rw [hr0, add_zero] at hzdec
      rcases eq_or_ne g 0 with hg0 | hg0
      · exfalso
        have hzW : z < Om (1 + 1) := by
          have h1 := sgLW_lt z
          rw [← hg, hg0, zero_add, leWe_one] at h1; exact h1
        exact absurd (hzW.trans tgOm_lt_G) (not_lt.2 hGz)
      · have hgpos : 0 < uaTh S l g := uaPos hl hX hgH (pos_iff_ne_zero.2 hg0) (hs.trans hzG)
        have hOlim : IsSuccLimit (leOe (uaTh S l g)) := by
          unfold leOe
          exact Ph.ph_opow_lim (mul_ne_zero (Om_pos one_ne_zero).ne' hgpos.ne')
        have hΘd : 0 < gxTh (upsilon l) (ldAtR S l) (z / leWe g) := by
          have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
          rw [sqTh_one hl hX] at h
          exact zero_lt_one.trans_le h
        exact isSuccLimit_mul_left hOlim hΘd
    · have hrlim : IsSuccLimit (z % leWe g) := by
        rcases zero_or_succ_or_isSuccLimit (z % leWe g) with h | ⟨r1, hr1⟩ | h
        · exact absurd h hr0
        · exfalso
          rw [succ_eq_add_one] at hr1
          have hz2 : z = leWe g * (z / leWe g) + r1 + 1 := by rw [add_assoc, hr1]; exact hzdec
          have h := hlim.succ_lt (lt_of_lt_of_eq (lt_add_one (leWe g * (z / leWe g) + r1)) hz2.symm)
          rw [Order.succ_eq_add_one, ← hz2] at h
          exact lt_irrefl _ h
        · exact h
      have hrz : z % leWe g < z := hrg.trans_le (sgLW_le h0)
      exact isSuccLimit_add _ (IH _ hrz hrH hrlim (hrz.trans hzG))
  · obtain ⟨-, hv, ha0, haE, -, -, -⟩ := uaNode hGz hzG hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hzH) (by rw [hv]; exact haE)
      (by rw [hv]; exact (uaNode hGz hzG hs).2.2.2.2.1)
    rw [(uaNodeTh hl hX hzH hGz hzG hs).1]
    exact taVeb_lim (uaPos hl hX hmem.1 ha0 (haE.trans hzG)).ne'

/-- **A tower dominating a normal fixed point gives countable members** (image `T`). -/
theorem uaMA_tow {E N : Ordinal.{0}} (f g fh gh : Ordinal.{0} → Ordinal.{0})
    (hEG : E < uaGam) (hNH : N ∈ cdHull S l) (hNE : N + 1 < E)
    (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x) (hE : E = nfp f (N + 1))
    (hfhm : Monotone fh) (hfgh : ∀ x, fh x ≤ gh x) (hEh : uaTh S l E = nfp fh (uaTh S l N + 1))
    (hg : ∀ x, x ∈ cdHull S l → N < x → x < E → g x ∈ cdHull S l ∧ g x < E ∧ x ≤ g x)
    (hTg : ∀ x, x ∈ cdHull S l → N < x → x < E → uaTh S l (g x) = gh (uaTh S l x))
    (hcN : ∀ Q, SC Q → ∀ h, LeCl (Om (1 + 1)) Q h → N < h → h ≤ E → LeCl (Om (1 + 1)) Q N)
    (hcg : ∀ Q, SC Q → ∀ x h, LeCl (Om (1 + 1)) Q h → N < x → g x ≤ h → h ≤ E →
      LeCl (Om (1 + 1)) Q x → LeCl (Om (1 + 1)) Q (g x)) :
    UaMA S l E := by
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
  have hNG : N + 1 < uaGam := hNE.trans hEG
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
    have hu0 : uaTh S l N + 1 ≤ uaTh S l (u 0) := (uaSucc hl hX hNH hNG).symm.le
    obtain ⟨j, hj⟩ := taTw_cof hfhm hfgh hw (fun j => uaTh S l (u j)) hu0
      (fun j => by
        show uaTh S l (u (j + 1)) = gh (uaTh S l (u j))
        rw [hus]; exact hTg _ (hu j).1 (hu j).2.2 (hu j).2.1)
    refine ⟨_, ⟨j, rfl⟩, hj.trans_le ?_⟩
    exact uaLe hl hX (hu j).1 (hu (j + 1)).1 ((hu (j + 1)).2.1.trans hEG) (hstep j)
  · rintro Q hQ m h ⟨j, rfl⟩ h1 h2 hh
    have hNc : LeCl (Om (1 + 1)) Q N := hcN Q hQ h hh ((hu (j + 1)).2.2.trans_le h1) h2
    have key : ∀ i, i ≤ j + 1 → LeCl (Om (1 + 1)) Q (u i) := by
      intro i
      induction i with
      | zero => intro _; exact LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ))
      | succ i ih =>
        intro hi
        have hle : u (i + 1) ≤ h := (hmono hi).trans h1
        rw [hus] at hle ⊢
        exact hcg Q hQ (u i) h hh (hu i).2.2 hle h2 (ih (Nat.le_of_succ_le hi))
    exact key (j + 1) le_rfl

/-- **`φ(1, y' + 1)` (`F_u ≤ φ(1, y')`, `φ(1, y' + 1) < F_{u+1}`, `u ≥ 1`) has countable members**: the tower
`W^·`. -/
theorem uaMA_towW {u y' : Ordinal.{0}} (hu1 : 1 ≤ u) (hy'H : y' ∈ cdHull S l)
    (hFN : veblen (Om (1 + 1)) u ≤ veblen 1 y') (hEX : veblen 1 (y' + 1) < veblen (Om (1 + 1)) (u + 1))
    (hEG : veblen 1 (y' + 1) < uaGam) : UaMA S l (veblen 1 (y' + 1)) := by
  have hGN : veblen (Om (1 + 1)) 1 ≤ veblen 1 y' := (uaG_le_F hu1).trans hFN
  set E := veblen 1 (y' + 1) with hE_def
  set N := veblen 1 y' with hN_def
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := CSet.one_mem _ _
  have hNH : N ∈ cdHull S l := CSet.phi_mem h1H hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim one_ne_zero
  have hEfix : ω ^ E = E := gg_veblen_eps one_ne_zero
  have hGE : veblen (Om (1 + 1)) 1 ≤ E := hGN.trans hNE.le
  have hΩE : Om (1 + 1) < E := tgOm_lt_G.trans_le hGE
  have hT1 : uaTh S l 1 = 1 := by rw [uaThCode hl hX hW1, sqTh_one hl hX]
  have hy'1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTE : uaTh S l E = veblen 1 (uaTh S l y' + 1) := by
    rw [uaVeb hl hX h1H (CSet.succ_mem hy'H) one_ne_zero hGE hEG, hT1, uaSucc hl hX hy'H hy'1G]
  have hTN : uaTh S l N = veblen 1 (uaTh S l y') := by
    rw [uaVeb hl hX h1H hy'H one_ne_zero hGN (hNE.trans hEG), hT1]
  refine uaMA_tow hl hX (veblen 0) leWe (veblen 0) leOe hEG hNH (hElim.add_one_lt hNE)
    (veblen_right_strictMono 0).monotone ?_ ?_ (veblen_right_strictMono 0).monotone ?_ ?_ ?_ ?_ ?_ ?_
  · intro x; rw [veblen_zero_apply]; unfold leWe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x ldOm2_SC.1)
  · have h := taVeb_succ 0 y'
    rw [zero_add] at h
    exact h
  · intro x; rw [veblen_zero_apply]; unfold leOe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x (Om_pos one_ne_zero))
  · have h := taVeb_succ 0 (uaTh S l y')
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
    have h := uaAddW hl hX (CSet.zero_mem _ _) hxH (dvd_zero _) (by rw [zero_add]; exact hWE.trans hEG)
    rwa [zero_add, uaTh_zero, zero_add] at h
  · intro Q hQ h hh h1 h2
    exact uaCl_NWin hQ hW1 hFN hh h1 h2 (h2.trans_lt hEX)
  · intro Q hQ x h _ _ _ _ hx
    exact tuWe_clX hQ hx

/-- **`φ(a' + 1, y' + 1)` (`a' ≥ 1`) has countable members**: the tower `φ(a', ·)` above `N + 1`. -/
theorem uaMA_towV {u a' y' : Ordinal.{0}} (hu1 : 1 ≤ u) (ha'H : a' ∈ cdHull S l) (ha'1 : 1 ≤ a')
    (haW : a' + 1 < Om (1 + 1)) (hy'H : y' ∈ cdHull S l) (hFN : veblen (Om (1 + 1)) u ≤ veblen (a' + 1) y')
    (hEX : veblen (a' + 1) (y' + 1) < veblen (Om (1 + 1)) (u + 1)) (hEG : veblen (a' + 1) (y' + 1) < uaGam) :
    UaMA S l (veblen (a' + 1) (y' + 1)) := by
  have hGN : veblen (Om (1 + 1)) 1 ≤ veblen (a' + 1) y' := (uaG_le_F hu1).trans hFN
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
  have hGE : veblen (Om (1 + 1)) 1 ≤ E := hGN.trans hNE.le
  have hy'1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hΘa : uaTh S l (a' + 1) = gxTh (upsilon l) (ldAtR S l) a' + 1 := by
    rw [uaThCode hl hX haW, gxTh_add hρSC hAt ha'c, sqTh_one hl hX]
  have hTE : uaTh S l E = veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (uaTh S l y' + 1) := by
    rw [uaVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEG, hΘa, uaSucc hl hX hy'H hy'1G]
  have hTN : uaTh S l N = veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (uaTh S l y') := by
    rw [uaVeb hl hX haH hy'H ha0 hGN (hNE.trans hEG), hΘa]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  refine uaMA_tow hl hX (veblen a') (veblen a') (veblen (gxTh (upsilon l) (ldAtR S l) a'))
    (veblen (gxTh (upsilon l) (ldAtR S l) a')) hEG hNH (hElim.add_one_lt hNE)
    (veblen_right_strictMono a').monotone (fun x => le_rfl) (taVeb_succ a' _)
    (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, hTN, taVeb_succ]
  · intro x hxH _ hxE
    refine ⟨CSet.phi_mem ha'H hxH, ?_, right_le_veblen _ _⟩
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hxE
      _ = E := hfix
  · intro x hxH hNx hxE
    have hvG : veblen (Om (1 + 1)) 1 ≤ veblen a' x := (hGN.trans hNx.le).trans (right_le_veblen _ _)
    have hlt : veblen a' x < E := by
      calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hxE
        _ = E := hfix
    rw [uaVeb hl hX ha'H hxH ha'0 hvG (hlt.trans hEG), uaThCode hl hX ha'W]
  · intro Q hQ h hh h1 h2
    exact uaCl_NWin hQ haW hFN hh h1 h2 (h2.trans_lt hEX)
  · intro Q hQ x h hh hNx hgx h2 hx
    have hFx : veblen (Om (1 + 1)) u < veblen a' x := (hFN.trans_lt hNx).trans_le (right_le_veblen _ _)
    have ha'c' := uaCl_levW hQ ha'W hFx h hh hgx (h2.trans_lt hEX)
    exact LeCl.phi ha'c' hx

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua
