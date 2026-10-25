import Googology.Trans.PoR.InaccPsi.R2.TxMSA

/-!
# Member systems of the Veblen nodes `φ(a, Ω₂ + z) < G`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
`N = φ(a, Ω₂ + z')`, member systems `Tu.TuMA`, `Tu.TuMB`.

* `txThLim` (`Θ a` is a limit for a limit code `a`), `txLimT` (`Θ̂_L z` is a limit for a limit `z ∈ H_λ ∩ G`);
* `txTw` (a tower `u 0 = b`, `u (j+1) = g (u j)`), `txMA_tow` (**a tower dominating a normal fixed point, with an
  image tower dominating the image fixed point, gives countable members**);
* `txMA_towW` (**`φ(1, Ω₂ + z' + 1)`: the tower of `W^·` above `N + 1`**), `txMA_towV` (**`φ(a' + 1, Ω₂ + z' + 1)`,
  `a' ≥ 1`: the tower of `φ(a', Ω₂ + ·)` above `N + 1`**), `txMA_levLim` (**a limit level `a`: the members
  `φ(c', Ω₂ + N + 1)`, `1 ≤ c' < a`**), `txMA_argLim`, `txMB_argLim` (**a limit argument `z`: the members of `z`
  lifted through `φ(a, Ω₂ + ·)`**);
* `txNodeMS` (**every node has a member system**, given one for its limit argument).

The own transfer (A3)/(B3) at a node comes from `Tx.txCl_lev`, `Tx.txCl_N`, `Tx.txCl_arg`.

No new axiom.  New definition: `txTw` (an `ℕ`-indexed tower).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

/-- **A tower** `u 0 = b`, `u (j + 1) = g (u j)`. -/
noncomputable def txTw (g : Ordinal.{0} → Ordinal.{0}) (b : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => b
  | j + 1 => g (txTw g b j)

/-- `Ω₂ + x < E` for `x < E = φ(a, y) > Ω₂`. -/
theorem txOm2_add_lt {a y x : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen a y) (hx : x < veblen a y) :
    Om (1 + 1) + x < veblen a y := Ph.ph_veblen_prin a y hΩ hx

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Θ a` is a limit for a limit code `a`.** -/
theorem txThLim {a : Ordinal.{0}} (hac : GxCl (upsilon l) (ldAtR S l) a) (hlim : IsSuccLimit a)
    (haW : a < Om (1 + 1)) : IsSuccLimit (gxTh (upsilon l) (ldAtR S l) a) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have h1 : (1 : Ordinal.{0}) ≤ gxTh (upsilon l) (ldAtR S l) a := by
    have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) (rvLim_one_lt hlim).le
    rwa [sqTh_one hl hX] at h
  rcases zero_or_succ_or_isSuccLimit (gxTh (upsilon l) (ldAtR S l) a) with h0 | ⟨d, hd⟩ | h
  · rw [h0] at h1; exact absurd h1 (not_le.2 zero_lt_one)
  · exfalso
    rw [succ_eq_add_one] at hd
    obtain ⟨c0, hc0, hc0a, e0⟩ := gxTh_onto (Z := upsilon l) (At := ldAtR S l) (m := a) (v := d)
      (by rw [← hd]; exact lt_add_one d)
    have hc1 : c0 + 1 < a := hlim.add_one_lt hc0a
    have hc1c : GxCl (upsilon l) (ldAtR S l) (c0 + 1) := rqCode_succ hl hX hc0 (hc1.trans haW)
    have h2 := gxTh_lt hc1c hc1
    rw [gxTh_add hρSC hAt hc0, sqTh_one hl hX, e0, hd] at h2
    exact lt_irrefl _ h2
  · exact h

/-- **`Θ̂_L z` is a limit for a limit `z ∈ H_λ ∩ G`.** -/
theorem txLimT : ∀ z, z ∈ cdHull S l → IsSuccLimit z → z < veblen (Om (1 + 1)) 1 →
    IsSuccLimit (tdThL S l z) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzH hlim hzG
  have h0 : 0 < z := hlim.bot_lt
  by_cases hs : sgLW z < z
  · obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hzdec, hT, -⟩ := txParts hl hX hzH h0 hzG
    set g := sgLW z with hg
    rw [hT]
    rcases eq_or_ne (z % leWe g) 0 with hr0 | hr0
    · rw [hr0, tjThL_zero, add_zero]
      rw [hr0, add_zero] at hzdec
      rcases eq_or_ne g 0 with hg0 | hg0
      · have hTg : leOe (tdThL S l g) = 1 := by rw [hg0, tjThL_zero, leOe_zero]
        have hzd : z / leWe g = z := by rw [hg0, leWe_zero, Ordinal.div_one]
        have hdlim : IsSuccLimit (z / leWe g) := by rw [hzd]; exact hlim
        rw [hTg, one_mul]
        exact txThLim hl hX hdc hdlim hdW
      · have hgpos : 0 < tdThL S l g := txPos hl hX hgH (pos_iff_ne_zero.2 hg0) (hs.trans hzG)
        have hOlim : IsSuccLimit (leOe (tdThL S l g)) := by
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
  · obtain ⟨a, w, hze, h1a, haW, hw1, hlt, -, hwH, -⟩ := txNode hl hX hzH h0 hzG hs
    rw [hze, (txNodeTh hl hX h1a haW hw1 hwH (hze ▸ hlt) (hze ▸ hzG)).1]
    have hΘa : gxTh (upsilon l) (ldAtR S l) a ≠ 0 := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) h1a
      rw [sqTh_one hl hX] at h
      exact (zero_lt_one.trans_le h).ne'
    exact taVeb_lim hΘa

/-- **A tower dominating a normal fixed point gives countable members**: `E = nfp f (N + 1)`, `Θ̂_L E = nfp f̂
(Θ̂_L N + 1)`, `g ≥ f`, `ĝ ≥ f̂`, `Θ̂_L (g x) = ĝ (Θ̂_L x)`, own transfers for `N` and along `g`. -/
theorem txMA_tow {E N : Ordinal.{0}} (f g fh gh : Ordinal.{0} → Ordinal.{0})
    (hEG : E < veblen (Om (1 + 1)) 1) (hNH : N ∈ cdHull S l) (hNE : N + 1 < E)
    (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x) (hE : E = nfp f (N + 1))
    (hfhm : Monotone fh) (hfgh : ∀ x, fh x ≤ gh x) (hEh : tdThL S l E = nfp fh (tdThL S l N + 1))
    (hg : ∀ x, x ∈ cdHull S l → x < E → g x ∈ cdHull S l ∧ g x < E ∧ x ≤ g x)
    (hTg : ∀ x, x ∈ cdHull S l → x < E → tdThL S l (g x) = gh (tdThL S l x))
    (hcN : ∀ Q, SC Q → ∀ h, LeCl (Om (1 + 1)) Q h → N < h → h ≤ E → LeCl (Om (1 + 1)) Q N)
    (hcg : ∀ Q, SC Q → ∀ x h, LeCl (Om (1 + 1)) Q h → N < x → g x ≤ h → h ≤ E →
      LeCl (Om (1 + 1)) Q x → LeCl (Om (1 + 1)) Q (g x)) :
    TuMA S l E := by
  set u := txTw g (N + 1) with hu_def
  have hus : ∀ j, u (j + 1) = g (u j) := fun j => rfl
  have hu : ∀ j, u j ∈ cdHull S l ∧ u j < E ∧ N < u j := by
    intro j
    induction j with
    | zero => exact ⟨CSet.succ_mem hNH, hNE, lt_add_one N⟩
    | succ j ih =>
      obtain ⟨a1, a2, a3⟩ := hg (u j) ih.1 ih.2.1
      rw [hus]
      exact ⟨a1, a2, ih.2.2.trans_le a3⟩
  have hstep : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hus]; exact (hg (u j) (hu j).1 (hu j).2.1).2.2
  have hmono : Monotone u := monotone_nat_of_le_succ hstep
  have hNG : N + 1 < veblen (Om (1 + 1)) 1 := hNE.trans hEG
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
    have hu0 : tdThL S l N + 1 ≤ tdThL S l (u 0) := (txSucc hl hX hNH hNG).symm.le
    obtain ⟨j, hj⟩ := taTw_cof hfhm hfgh hw (fun j => tdThL S l (u j)) hu0
      (fun j => by
        show tdThL S l (u (j + 1)) = gh (tdThL S l (u j))
        rw [hus]; exact hTg _ (hu j).1 (hu j).2.1)
    refine ⟨_, ⟨j, rfl⟩, hj.trans_le ?_⟩
    exact txLe hl hX (hu j).1 (hu (j + 1)).1 ((hu (j + 1)).2.1.trans hEG) (hstep j)
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

/-- **`φ(1, Ω₂ + z' + 1)` has countable members**: the tower `W^·` above `φ(1, Ω₂ + z') + 1`. -/
theorem txMA_towW {z' : Ordinal.{0}} (hz'H : z' ∈ cdHull S l)
    (hEG : veblen 1 (Om (1 + 1) + z' + 1) < veblen (Om (1 + 1)) 1) :
    TuMA S l (veblen 1 (Om (1 + 1) + z' + 1)) := by
  set E := veblen 1 (Om (1 + 1) + z' + 1) with hE_def
  set N := veblen 1 (Om (1 + 1) + z') with hN_def
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := CSet.one_mem _ _
  have hNH : N ∈ cdHull S l := CSet.phi_mem h1H (CSet.add_mem (mxOm2_mem _ _) hz'H)
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim one_ne_zero
  have hEfix : ω ^ E = E := gg_veblen_eps one_ne_zero
  have hΩE : Om (1 + 1) < E := by
    have h := taKy_lt (κ := Om (1 + 1)) (a := 1) (le_add_self : (1 : Ordinal.{0}) ≤ z' + 1)
    rw [← add_assoc] at h
    exact h
  have hz1G : z' + 1 < veblen (Om (1 + 1)) 1 := by
    refine lt_of_le_of_lt ?_ hEG
    calc z' + 1 ≤ Om (1 + 1) + (z' + 1) := le_add_self
      _ = Om (1 + 1) + z' + 1 := (add_assoc _ _ _).symm
      _ ≤ veblen _ _ := right_le_veblen _ _
  have hTE : tdThL S l E = veblen 1 (Om 1 + tdThL S l z' + 1) := by
    have h := txVeb hl hX h1H le_rfl hW1 (CSet.succ_mem hz'H) (by rw [← add_assoc]; exact hEG)
    rw [← add_assoc, sqTh_one hl hX, txSucc hl hX hz'H hz1G, ← add_assoc] at h
    exact h
  have hTN : tdThL S l N = veblen 1 (Om 1 + tdThL S l z') := by
    have h := txVeb hl hX h1H le_rfl hW1 hz'H (hNE.trans hEG)
    rwa [sqTh_one hl hX] at h
  refine txMA_tow hl hX (veblen 0) leWe (veblen 0) leOe hEG hNH (hElim.add_one_lt hNE)
    (veblen_right_strictMono 0).monotone ?_ ?_ (veblen_right_strictMono 0).monotone ?_ ?_ ?_ ?_ ?_ ?_
  · intro x; rw [veblen_zero_apply]; unfold leWe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x ldOm2_SC.1)
  · have h := taVeb_succ 0 (Om (1 + 1) + z')
    rw [zero_add] at h
    exact h
  · intro x; rw [veblen_zero_apply]; unfold leOe
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right x (Om_pos one_ne_zero))
  · have h := taVeb_succ 0 (Om 1 + tdThL S l z')
    rw [zero_add] at h
    rw [hTE, hTN, h]
  · intro x hxH hxE
    refine ⟨leWe_mem hxH, ?_, tnLe_We x⟩
    unfold leWe; conv_rhs => rw [← hEfix]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix hEfix hΩE hxE)
  · intro x hxH hxE
    have hWE : leWe x < E := by
      unfold leWe; conv_rhs => rw [← hEfix]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (tuMul_lt_fix hEfix hΩE hxE)
    have h := txAddW hl hX (CSet.zero_mem _ _) hxH (dvd_zero _) (by rw [zero_add]; exact hWE.trans hEG)
    rwa [zero_add, tjThL_zero, zero_add] at h
  · intro Q hQ h hh h1 h2
    exact txCl_N hQ hW1 hh h1 h2 (h2.trans_lt hEG)
  · intro Q hQ x h _ _ _ _ hx
    exact tuWe_clX hQ hx

/-- **`φ(a' + 1, Ω₂ + z' + 1)` (`a' ≥ 1`) has countable members**: the tower `φ(a', Ω₂ + ·)` above
`φ(a' + 1, Ω₂ + z') + 1`. -/
theorem txMA_towV {a' z' : Ordinal.{0}} (ha'H : a' ∈ cdHull S l) (ha'1 : 1 ≤ a') (haW : a' + 1 < Om (1 + 1))
    (hz'H : z' ∈ cdHull S l) (hEG : veblen (a' + 1) (Om (1 + 1) + z' + 1) < veblen (Om (1 + 1)) 1) :
    TuMA S l (veblen (a' + 1) (Om (1 + 1) + z' + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set E := veblen (a' + 1) (Om (1 + 1) + z' + 1) with hE_def
  set N := veblen (a' + 1) (Om (1 + 1) + z') with hN_def
  have ha'W : a' < Om (1 + 1) := (lt_add_one a').trans haW
  have haH : a' + 1 ∈ cdHull S l := CSet.succ_mem ha'H
  have ha'c : GxCl (upsilon l) (ldAtR S l) a' := (ldHull_iff hl hX ha'W).1 ha'H
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH (CSet.add_mem (mxOm2_mem _ _) hz'H)
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have hΩE : Om (1 + 1) < E := by
    have h := taKy_lt (κ := Om (1 + 1)) (a := a' + 1) (le_add_self : (1 : Ordinal.{0}) ≤ z' + 1)
    rw [← add_assoc] at h
    exact h
  have hz1G : z' + 1 < veblen (Om (1 + 1)) 1 := by
    refine lt_of_le_of_lt ?_ hEG
    calc z' + 1 ≤ Om (1 + 1) + (z' + 1) := le_add_self
      _ = Om (1 + 1) + z' + 1 := (add_assoc _ _ _).symm
      _ ≤ veblen _ _ := right_le_veblen _ _
  have hΘa : gxTh (upsilon l) (ldAtR S l) (a' + 1) = gxTh (upsilon l) (ldAtR S l) a' + 1 := by
    rw [gxTh_add hρSC hAt ha'c, sqTh_one hl hX]
  have hTE : tdThL S l E =
      veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (Om 1 + tdThL S l z' + 1) := by
    have h := txVeb hl hX haH le_add_self haW (CSet.succ_mem hz'H) (by rw [← add_assoc]; exact hEG)
    rw [← add_assoc, hΘa, txSucc hl hX hz'H hz1G, ← add_assoc] at h
    exact h
  have hTN : tdThL S l N = veblen (gxTh (upsilon l) (ldAtR S l) a' + 1) (Om 1 + tdThL S l z') := by
    have h := txVeb hl hX haH le_add_self haW hz'H (hNE.trans hEG)
    rwa [hΘa] at h
  have hfix : ∀ x : Ordinal.{0}, veblen a' E = E := fun _ => veblen_veblen_of_lt (lt_add_one a') _
  refine txMA_tow hl hX (veblen a') (fun x => veblen a' (Om (1 + 1) + x))
    (veblen (gxTh (upsilon l) (ldAtR S l) a')) (fun x => veblen (gxTh (upsilon l) (ldAtR S l) a') (Om 1 + x))
    hEG hNH (hElim.add_one_lt hNE) (veblen_right_strictMono a').monotone
    (fun x => (veblen_le_veblen_iff_right).2 le_add_self) (taVeb_succ a' _)
    (veblen_right_strictMono _).monotone (fun x => (veblen_le_veblen_iff_right).2 le_add_self) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, hTN, taVeb_succ]
  · intro x hxH hxE
    refine ⟨CSet.phi_mem ha'H (CSet.add_mem (mxOm2_mem _ _) hxH), ?_,
      le_add_self.trans (right_le_veblen _ _)⟩
    calc veblen a' (Om (1 + 1) + x) < veblen a' E :=
          (veblen_lt_veblen_iff_right).2 (txOm2_add_lt hΩE hxE)
      _ = E := hfix x
  · intro x hxH hxE
    have hlt : veblen a' (Om (1 + 1) + x) < veblen (Om (1 + 1)) 1 := by
      calc veblen a' (Om (1 + 1) + x) < veblen a' E :=
            (veblen_lt_veblen_iff_right).2 (txOm2_add_lt hΩE hxE)
        _ = E := hfix x
        _ < _ := hEG
    exact txVeb hl hX ha'H ha'1 ha'W hxH hlt
  · intro Q hQ h hh h1 h2
    exact txCl_N hQ haW hh h1 h2 (h2.trans_lt hEG)
  · intro Q hQ x h hh hNx hgx h2 hx
    have hx1 : 1 ≤ x := Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le hNx)
    have ha'c' := txCl_lev hQ ha'W (taKy_lt hx1) h hh hgx (h2.trans_lt hEG)
    exact LeCl.phi ha'c' (LeCl.add LeCl.om hx)

/-- **A limit level `a`: countable members `φ(c', Ω₂ + N + 1)`, `1 ≤ c' < a`** (`N = φ(a, Ω₂ + z')`). -/
theorem txMA_levLim {a z' : Ordinal.{0}} (haH : a ∈ cdHull S l) (hlim : IsSuccLimit a) (haW : a < Om (1 + 1))
    (hz'H : z' ∈ cdHull S l) (hEG : veblen a (Om (1 + 1) + z' + 1) < veblen (Om (1 + 1)) 1) :
    TuMA S l (veblen a (Om (1 + 1) + z' + 1)) := by
  set E := veblen a (Om (1 + 1) + z' + 1) with hE_def
  set N := veblen a (Om (1 + 1) + z') with hN_def
  set M := Om (1 + 1) + (N + 1) with hM_def
  have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 haH
  have h1a : 1 ≤ a := (rvLim_one_lt hlim).le
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH (CSet.add_mem (mxOm2_mem _ _) hz'H)
  have hMH : M ∈ cdHull S l := CSet.add_mem (mxOm2_mem _ _) (CSet.succ_mem hNH)
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have hΩE : Om (1 + 1) < E := by
    have h := taKy_lt (κ := Om (1 + 1)) (a := a) (le_add_self : (1 : Ordinal.{0}) ≤ z' + 1)
    rw [← add_assoc] at h
    exact h
  have hME : M < E := txOm2_add_lt hΩE (hElim.add_one_lt hNE)
  have hmE : ∀ c', c' < a → veblen c' M < E := fun c' hc' => by
    calc veblen c' M < veblen c' E := (veblen_lt_veblen_iff_right).2 hME
      _ = E := veblen_veblen_of_lt hc' _
  have hz1G : z' + 1 < veblen (Om (1 + 1)) 1 := by
    refine lt_of_le_of_lt ?_ hEG
    calc z' + 1 ≤ Om (1 + 1) + (z' + 1) := le_add_self
      _ = Om (1 + 1) + z' + 1 := (add_assoc _ _ _).symm
      _ ≤ veblen _ _ := right_le_veblen _ _
  have hNG : N + 1 < veblen (Om (1 + 1)) 1 := (hElim.add_one_lt hNE).trans hEG
  have hTN : tdThL S l N = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z') :=
    txVeb hl hX haH h1a haW hz'H (hNE.trans hEG)
  have hTE : tdThL S l E = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z' + 1) := by
    have h := txVeb hl hX haH h1a haW (CSet.succ_mem hz'H) (by rw [← add_assoc]; exact hEG)
    rw [← add_assoc, txSucc hl hX hz'H hz1G, ← add_assoc] at h
    exact h
  have hTm : ∀ c', c' ∈ cdHull S l → 1 ≤ c' → c' < a →
      tdThL S l (veblen c' M) = veblen (gxTh (upsilon l) (ldAtR S l) c') (Om 1 + (tdThL S l N + 1)) := by
    intro c' hc'H hc'1 hc'a
    rw [txVeb hl hX hc'H hc'1 (hc'a.trans haW) (CSet.succ_mem hNH) ((hmE c' hc'a).trans hEG),
      txSucc hl hX hNH hNG]
  refine ⟨fun m => ∃ c', c' ∈ cdHull S l ∧ 1 ≤ c' ∧ c' < a ∧ m = veblen c' M, ?_,
    ⟨_, 1, CSet.one_mem _ _, le_rfl, rvLim_one_lt hlim, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨c', hc'H, -, hc'a, rfl⟩
    exact ⟨CSet.phi_mem hc'H hMH, Order.one_le_iff_pos.2 veblen_pos, hmE c' hc'a⟩
  · intro y hyH hy
    obtain ⟨c', hc'H, hc'a, hyc⟩ := tdHull_levDec hlim y hyH hy
    refine ⟨_, ⟨c' + 1, CSet.succ_mem hc'H, le_add_self, hlim.add_one_lt hc'a, rfl⟩, ?_⟩
    calc y < veblen c' (N + 1) := hyc
      _ ≤ veblen (c' + 1) (N + 1) := veblen_left_monotone (N + 1) le_self_add
      _ ≤ veblen (c' + 1) M := (veblen_le_veblen_iff_right).2 le_add_self
  · intro w hw
    rw [hTE] at hw
    obtain ⟨d, hd, hwd⟩ := taVeb_lim_cof (txThLim hl hX hac hlim haW) hw
    rw [← hTN] at hwd
    obtain ⟨c0, hc0, hc0a, e0⟩ := gxTh_onto (Z := upsilon l) (At := ldAtR S l) hd
    have hc1a : c0 + 1 < a := hlim.add_one_lt hc0a
    have hc1c : GxCl (upsilon l) (ldAtR S l) (c0 + 1) := rqCode_succ hl hX hc0 (hc1a.trans haW)
    have hc1H : c0 + 1 ∈ cdHull S l := (ldHull_iff hl hX (hc1a.trans haW)).2 hc1c
    obtain ⟨hρSC, -⟩ := leRho hl hX
    have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
    refine ⟨_, ⟨c0 + 1, hc1H, le_add_self, hc1a, rfl⟩, ?_⟩
    rw [hTm _ hc1H le_add_self hc1a, gxTh_add hρSC hAt hc0, sqTh_one hl hX, e0]
    calc w < veblen d (tdThL S l N + 1) := hwd
      _ ≤ veblen (d + 1) (tdThL S l N + 1) := veblen_left_monotone _ le_self_add
      _ ≤ veblen (d + 1) (Om 1 + (tdThL S l N + 1)) := (veblen_le_veblen_iff_right).2 le_add_self
  · rintro Q hQ m h ⟨c', -, hc'1, hc'a, rfl⟩ h1 h2 hh
    have hG : h < veblen (Om (1 + 1)) 1 := h2.trans_lt hEG
    have hc'c := txCl_lev hQ (hc'a.trans haW) (taKy_lt (le_add_self : (1 : Ordinal.{0}) ≤ N + 1)) h hh h1 hG
    have hNlt : N < h := (lt_add_one N).trans_le (le_add_self.trans ((right_le_veblen c' M).trans h1))
    have hNc := txCl_N hQ haW hh hNlt h2 hG
    exact LeCl.phi hc'c (LeCl.add LeCl.om (LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ))))

/-- **A limit argument `z` with countable members**: the members `φ(a, Ω₂ + m)`. -/
theorem txMA_argLim {a z : Ordinal.{0}} (haH : a ∈ cdHull S l) (h1a : 1 ≤ a) (haW : a < Om (1 + 1))
    (hzH : z ∈ cdHull S l) (hzlim : IsSuccLimit z) (hEG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1)
    (hA : TuMA S l z) : TuMA S l (veblen a (Om (1 + 1) + z)) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  set E := veblen a (Om (1 + 1) + z) with hE_def
  have hzG : z < veblen (Om (1 + 1)) 1 :=
    (le_add_self.trans (right_le_veblen a _)).trans_lt hEG
  have hmE : ∀ m, Mem m → veblen a (Om (1 + 1) + m) < E := fun m hm =>
    (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 (hdat m hm).2.2)
  have hTm : ∀ m, Mem m → tdThL S l (veblen a (Om (1 + 1) + m)) =
      veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l m) := fun m hm =>
    txVeb hl hX haH h1a haW (hdat m hm).1 ((hmE m hm).trans hEG)
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = veblen a (Om (1 + 1) + m), ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    exact ⟨CSet.phi_mem haH (CSet.add_mem (mxOm2_mem _ _) (hdat m hm).1),
      Order.one_le_iff_pos.2 veblen_pos, hmE m hm⟩
  · intro y hyH hy
    have hm0le : veblen a 0 ≤ veblen a (Om (1 + 1) + m0) := (veblen_le_veblen_iff_right).2 zero_le
    by_cases h0 : veblen a 0 ≤ y
    swap
    · push Not at h0; exact ⟨_, ⟨m0, hm0, rfl⟩, h0.trans_le hm0le⟩
    obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hyH h0
    have huz : u < Om (1 + 1) + z := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hy)
    rcases lt_or_ge u (Om (1 + 1)) with huW | huW
    · refine ⟨_, ⟨m0, hm0, rfl⟩, hu2.trans_le ((veblen_le_veblen_iff_right).2 ?_)⟩
      exact (Order.add_one_le_of_lt huW).trans le_self_add
    have hv : Om (1 + 1) + (u - Om (1 + 1)) = u := Ordinal.add_sub_cancel_of_le huW
    have hvz : u - Om (1 + 1) < z := by
      have : Om (1 + 1) + (u - Om (1 + 1)) < Om (1 + 1) + z := by rw [hv]; exact huz
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨m, hm, hvm⟩ := hA1 _ (Ta.taSub_mem (S := S) _ huH _) hvz
    refine ⟨_, ⟨m, hm, rfl⟩, hu2.trans_le ((veblen_le_veblen_iff_right).2 ?_)⟩
    rw [← hv, add_assoc]
    exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hvm)
  · intro w hw
    rw [txVeb hl hX haH h1a haW hzH hEG] at hw
    have hXlim : IsSuccLimit (Om 1 + tdThL S l z) := isSuccLimit_add _ (txLimT hl hX z hzH hzlim hzG)
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hXlim).1 hw
    rcases le_or_gt u' (Om 1) with hu1 | hu1
    · refine ⟨_, ⟨m0, hm0, rfl⟩, ?_⟩
      rw [hTm m0 hm0]
      exact hwu.trans_le ((veblen_le_veblen_iff_right).2 (hu1.trans le_self_add))
    have hv : Om 1 + (u' - Om 1) = u' := Ordinal.add_sub_cancel_of_le hu1.le
    have hvz : u' - Om 1 < tdThL S l z := by
      have : Om 1 + (u' - Om 1) < Om 1 + tdThL S l z := by rw [hv]; exact hu'
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨m, hm, hvm⟩ := hA2 _ hvz
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    refine hwu.trans ((veblen_lt_veblen_iff_right).2 ?_)
    rw [← hv]; exact (add_lt_add_iff_left _).2 hvm
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    obtain ⟨hac', v, hv, hmv, hvz⟩ := txCl_arg hQ haW (hdat m hm).2.1 hh h1 h2 (h2.trans_lt hEG)
    exact LeCl.phi hac' (LeCl.add LeCl.om (hA3 Q hQ m v hm hmv hvz hv))

/-- **A limit argument `z` with members indexed by the codes**: the members `φ(a, Ω₂ + M c)`. -/
theorem txMB_argLim {a z : Ordinal.{0}} (haH : a ∈ cdHull S l) (h1a : 1 ≤ a) (haW : a < Om (1 + 1))
    (hzH : z ∈ cdHull S l) (hzlim : IsSuccLimit z) (hEG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1)
    (hB : TuMB S l z) : TuMB S l (veblen a (Om (1 + 1) + z)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen a (Om (1 + 1) + z) with hE_def
  set Θa := gxTh (upsilon l) (ldAtR S l) a with hΘa_def
  have hΘaO : Θa < Om 1 := snTh_lt_Om1 hl hX haW.le
  have hzG : z < veblen (Om (1 + 1)) 1 :=
    (le_add_self.trans (right_le_veblen a _)).trans_lt hEG
  have hTE : tdThL S l E = veblen Θa (Om 1 + tdThL S l z) := txVeb hl hX haH h1a haW hzH hEG
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  obtain ⟨hM1H, hM11, hM1z, hTM1, -⟩ := hB0 1 hc1 le_rfl hW1
  have hMh1 : 0 < Mh 1 := by
    rw [sqTh_one hl hX] at hTM1
    rw [← hTM1]
    exact txPos hl hX hM1H (zero_lt_one.trans_le hM11) (hM1z.trans hzG)
  refine ⟨fun c => veblen a (Om (1 + 1) + M c), fun c => veblen Θa (Om 1 + Mh c),
    fun x y h => (veblen_le_veblen_iff_right).2 ((add_le_add_iff_left _).2 (hM h)),
    fun x y h => (veblen_le_veblen_iff_right).2 ((add_le_add_iff_left _).2 (hMh h)), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, hM1, hMz, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    have hlt : veblen a (Om (1 + 1) + M c) < E :=
      (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 hMz)
    refine ⟨CSet.phi_mem haH (CSet.add_mem (mxOm2_mem _ _) hMH), Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [txVeb hl hX haH h1a haW hMH (hlt.trans hEG), hTM]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2 hMhT)
  · intro Q hQ hQ1 w hw hwE
    have hXlim : IsSuccLimit (Om (1 + 1) + z) := isSuccLimit_add _ hzlim
    obtain ⟨u, hu, huz, hwu⟩ := taCl_dec hQ ldOm2_SC haW hXlim w hw hwE
    rcases le_or_gt u (Om (1 + 1)) with huW | huW
    · exact ⟨1, gg_one_lt_of_SC hQ, hwu.trans_le ((veblen_le_veblen_iff_right).2 (huW.trans le_self_add))⟩
    have hv : Om (1 + 1) + (u - Om (1 + 1)) = u := Ordinal.add_sub_cancel_of_le huW.le
    have hvz : u - Om (1 + 1) < z := by
      have : Om (1 + 1) + (u - Om (1 + 1)) < Om (1 + 1) + z := by rw [hv]; exact huz
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨c', hc'Q, hvc'⟩ := hB1 Q hQ hQ1 _ (txCl_subK hQ ldOm2_SC hu huW.le) hvz
    refine ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 ?_)⟩
    rw [← hv]; exact (add_lt_add_iff_left _).2 hvc'
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    have hXlim : IsSuccLimit (Om 1 + tdThL S l z) := isSuccLimit_add _ (txLimT hl hX z hzH hzlim hzG)
    obtain ⟨u, hu, huz, hwu⟩ := taCl_dec hQ Ph.ph_SC_Om1 hΘaO hXlim w hw hwE
    rcases le_or_gt u (Om 1) with hu1 | hu1
    · refine ⟨1, gg_one_lt_of_SC hQ, hwu.trans_le ((veblen_le_veblen_iff_right).2 ?_)⟩
      exact hu1.trans le_self_add
    have hv : Om 1 + (u - Om 1) = u := Ordinal.add_sub_cancel_of_le hu1.le
    have hvz : u - Om 1 < tdThL S l z := by
      have : Om 1 + (u - Om 1) < Om 1 + tdThL S l z := by rw [hv]; exact huz
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨c', hc'Q, hvc'⟩ := hB2 Q hQ _ (txCl_subK hQ Ph.ph_SC_Om1 hu hu1.le) hvz
    refine ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 ?_)⟩
    rw [← hv]; exact (add_lt_add_iff_left _).2 hvc'
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    rcases eq_or_ne (M c) 0 with hM0 | hM0
    · show LeCl (Om (1 + 1)) Q (veblen a (Om (1 + 1) + M c))
      rw [hM0, add_zero, ldOm2_SC.veblen_right haW]; exact LeCl.om
    obtain ⟨hac', v, hv, hmv, hvz⟩ :=
      txCl_arg hQ haW (Order.one_le_iff_ne_zero.2 hM0) hh h1 h2 (h2.trans_lt hEG)
    exact LeCl.phi hac' (LeCl.add LeCl.om (hB3 Q hQ c v hc1' hcQ hmv hvz hv))

/-- **Every node `φ(a, Ω₂ + z) < G` of `H_λ` has a member system**, given one for its argument `z` when `z` is a
limit. -/
theorem txNodeMS {a z : Ordinal.{0}} (haH : a ∈ cdHull S l) (h1a : 1 ≤ a) (haW : a < Om (1 + 1))
    (hzH : z ∈ cdHull S l) (hz1 : 1 ≤ z) (hEG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1)
    (IH : IsSuccLimit z → TuMA S l z ∨ TuMB S l z) :
    TuMA S l (veblen a (Om (1 + 1) + z)) ∨ TuMB S l (veblen a (Om (1 + 1) + z)) := by
  rcases zero_or_succ_or_isSuccLimit z with h0 | ⟨z', hz'⟩ | hzl
  · rw [h0] at hz1; exact absurd hz1 (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hz'
    subst hz'
    have hz'H : z' ∈ cdHull S l := mem_of_add_one_mem hzH
    rw [← add_assoc] at hEG ⊢
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at h1a; exact absurd h1a (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      have ha'H : a' ∈ cdHull S l := mem_of_add_one_mem haH
      rcases eq_or_ne a' 0 with rfl | ha'0
      · rw [zero_add] at hEG ⊢
        exact Or.inl (txMA_towW hl hX hz'H hEG)
      · exact Or.inl (txMA_towV hl hX ha'H (Order.one_le_iff_ne_zero.2 ha'0) haW hz'H hEG)
    · exact Or.inl (txMA_levLim hl hX haH hal haW hz'H hEG)
  · rcases IH hzl with hA | hB
    · exact Or.inl (txMA_argLim hl hX haH h1a haW hzH hzl hEG hA)
    · exact Or.inr (txMB_argLim hl hX haH h1a haW hzH hzl hEG hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx
