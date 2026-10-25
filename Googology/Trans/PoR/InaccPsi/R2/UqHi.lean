import Googology.Trans.PoR.InaccPsi.R2.UqCodeHi

/-!
# Member systems of the nodes `φ(a, y)` with a level `a > Ω₂` past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q`, `G = φ(Ω₂, 1)`,
`Y₃ = ψ_{Ω₃}(Ω₃)`, member systems `Uq.UqMA`, `Uq.UqMB`.

`Ud.udMA_tow`, `Ud.udMA_succ`, `Ud.udMA_zero`, `Ud.udMA_levLim`, `Ud.udMB_levLim`, `Ud.udMA_lev0`, `Ud.udMB_lev0`,
`Ud.udMA_argLim`, `Ud.udMB_argLim`, `Ud.udNodeHi` with the bound `Y₃` in place of `Γ₂`: the image `T` (`Uq.uqVeb`,
`Ug.ugSucc`, `Ug.ugLt`, `Uq.uqLimT`), the level codes and the transfers `Uq.uqCl_N`, `Uq.uqCl_tow`, `Uq.uqCl_levGe`,
`Uq.uqCl_levDec`, `Uq.uqCl_levDec0`, `Uq.uqCl_decA`, `Uq.uqThr`, `Uq.uqOwn0`, `Uq.uqOwnArg`.

* `uqMA_towB` (a tower from a start `b ≥ 1` dominating a normal fixed point gives countable members);
* `uqMA_succ` (`φ(a' + 1, y' + 1)`, `a' ≥ Ω₂`), `uqMA_zero` (`φ(a' + 1, 0)`, `a' ≥ Ω₂`);
* `uqMA_levLimH`, `uqMB_levLimH` (`φ(a, y' + 1)`, `a > Ω₂` a limit), `uqMA_lev0`, `uqMB_lev0` (`φ(a, 0)`),
  `uqMA_argLimH`, `uqMB_argLimH` (`φ(a, y)`, `y` a limit);
* `uqNodeHi` (**EVERY NODE `φ(a, y) < Y₃` WITH A LEVEL `a > Ω₂` HAS A MEMBER SYSTEM**, given those of `a` and `y`
  when they are limits).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A tower from a start `b ≥ 1` dominating a normal fixed point gives countable members.** -/
theorem uqMA_towB {E b : Ordinal.{0}} (f g fh gh : Ordinal.{0} → Ordinal.{0})
    (hEG : E < ugY S) (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b) (hbE : b < E)
    (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x) (hE : E = nfp f b)
    (hfhm : Monotone fh) (hfgh : ∀ x, fh x ≤ gh x) (hEh : ugTh S l E = nfp fh (ugTh S l b))
    (hg : ∀ x, x ∈ cdHull S l → b ≤ x → x < E → g x ∈ cdHull S l ∧ g x < E ∧ x ≤ g x)
    (hTg : ∀ x, x ∈ cdHull S l → b ≤ x → x < E → ugTh S l (g x) = gh (ugTh S l x))
    (hcb : ∀ Q, SC Q → ∀ h, UgC S (1 + 1) Q h → b ≤ h → h ≤ E → UgC S (1 + 1) Q b)
    (hcg : ∀ Q, SC Q → ∀ x h, UgC S (1 + 1) Q h → b ≤ x → g x ≤ h → h ≤ E →
      UgC S (1 + 1) Q x → UgC S (1 + 1) Q (g x)) :
    UqMA S l E := by
  set u := txTw g b with hu_def
  have hus : ∀ j, u (j + 1) = g (u j) := fun j => rfl
  have hu : ∀ j, u j ∈ cdHull S l ∧ u j < E ∧ b ≤ u j := by
    intro j
    induction j with
    | zero => exact ⟨hbH, hbE, le_rfl⟩
    | succ j ih =>
      obtain ⟨a1, a2, a3⟩ := hg (u j) ih.1 ih.2.2 ih.2.1
      rw [hus]
      exact ⟨a1, a2, ih.2.2.trans a3⟩
  have hstep : ∀ j, u j ≤ u (j + 1) := fun j => by
    rw [hus]; exact (hg (u j) (hu j).1 (hu j).2.2 (hu j).2.1).2.2
  have hmono : Monotone u := monotone_nat_of_le_succ hstep
  refine ⟨fun m => ∃ j, m = u (j + 1), ?_, ⟨_, 0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨j, rfl⟩
    obtain ⟨a1, a2, a3⟩ := hu (j + 1)
    exact ⟨a1, hb1.trans a3, a2⟩
  · intro y _ hy
    rw [hE] at hy
    obtain ⟨j, hj⟩ := taTw_cof hfm hfg hy u le_rfl hus
    exact ⟨_, ⟨j, rfl⟩, hj.trans_le (hstep j)⟩
  · intro w hw
    rw [hEh] at hw
    obtain ⟨j, hj⟩ := taTw_cof hfhm hfgh hw (fun j => ugTh S l (u j)) le_rfl
      (fun j => by
        show ugTh S l (u (j + 1)) = gh (ugTh S l (u j))
        rw [hus]; exact hTg _ (hu j).1 (hu j).2.2 (hu j).2.1)
    refine ⟨_, ⟨j, rfl⟩, hj.trans_le ?_⟩
    exact ugLe hl hX (hu j).1 (hu (j + 1)).1 ((hu (j + 1)).2.1.trans hEG) (hstep j)
  · rintro Q hQ m h ⟨j, rfl⟩ h1 h2 hh
    have hbc : UgC S (1 + 1) Q b := hcb Q hQ h hh ((hu (j + 1)).2.2.trans h1) h2
    have key : ∀ i, i ≤ j + 1 → UgC S (1 + 1) Q (u i) := by
      intro i
      induction i with
      | zero => intro _; exact hbc
      | succ i ih =>
        intro hi
        have hle : u (i + 1) ≤ h := (hmono hi).trans h1
        rw [hus] at hle ⊢
        exact hcg Q hQ (u i) h hh (hu i).2.2 hle h2 (ih (Nat.le_of_succ_le hi))
    exact key (j + 1) le_rfl

/-- **`φ(a' + 1, y' + 1)` with `a' ≥ Ω₂`**: the tower `φ(a', ·)` above `N + 1`, `N = φ(a' + 1, y')`. -/
theorem uqMA_succ {a' y' : Ordinal.{0}} (ha'H : a' ∈ cdHull S l) (ha' : Om (1 + 1) ≤ a')
    (hy'H : y' ∈ cdHull S l) (hEG : veblen (a' + 1) (y' + 1) < ugY S) :
    UqMA S l (veblen (a' + 1) (y' + 1)) := by
  set E := veblen (a' + 1) (y' + 1) with hE_def
  set N := veblen (a' + 1) y' with hN_def
  have ha2 : Om (1 + 1) < a' + 1 := ha'.trans_lt (lt_add_one a')
  have ha'0 : a' ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans_le ha').ne'
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have haH : a' + 1 ∈ cdHull S l := CSet.succ_mem ha'H
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have hN1E : N + 1 < E := hElim.add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 < N := udG_lt ha2
  have hΩN : Om (1 + 1) < N := tgOm_lt_G.trans hGN
  have hGE : veblen (Om (1 + 1)) 1 ≤ E := (hGN.trans hNE).le
  have hNG : N < ugY S := hNE.trans hEG
  have ha1G : a' + 1 < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEG
  have hTa : ugTh S l (a' + 1) = ugTh S l a' + 1 := ugSucc hl hX ha'H ha1G
  have hTE : ugTh S l E = veblen (ugTh S l a' + 1) (ugTh S l y' + 1) := by
    rw [uqVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEG, hTa, ugSucc hl hX hy'H hy1G]
  have hTN : ugTh S l N = veblen (ugTh S l a' + 1) (ugTh S l y') := by
    rw [uqVeb hl hX haH hy'H ha0 hGN.le hNG, hTa]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  have hlt : ∀ x, x < E → veblen a' x < E := fun x hx => by
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hx
      _ = E := hfix
  refine uqMA_towB hl hX (veblen a') (veblen a') (veblen (ugTh S l a')) (veblen (ugTh S l a')) hEG
    (CSet.succ_mem hNH) le_add_self hN1E (veblen_right_strictMono a').monotone (fun x => le_rfl)
    (taVeb_succ a' y') (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, ugSucc hl hX hNH (hN1E.trans hEG), hTN, taVeb_succ]
  · intro x hxH _ hxE
    exact ⟨CSet.phi_mem ha'H hxH, hlt x hxE, right_le_veblen _ _⟩
  · intro x hxH hNx hxE
    have hvG : veblen (Om (1 + 1)) 1 ≤ veblen a' x :=
      (hGN.le.trans ((le_self_add.trans hNx).trans (right_le_veblen _ _)))
    exact uqVeb hl hX ha'H hxH ha'0 hvG ((hlt x hxE).trans hEG)
  · intro Q hQ h hh h1 h2
    exact UgC.add (uqCl_N hQ hΩN hh ((lt_add_one N).trans_le h1) h2) (UgC.small (gg_one_lt_of_SC hQ))
  · intro Q hQ x h hh hNx hgx h2 hx
    have hNx' : N < veblen a' x := (lt_add_one N).trans_le (hNx.trans (right_le_veblen _ _))
    have hy : y' + 1 < E := hElim.add_one_lt ((right_le_veblen _ _).trans_lt hNE)
    have ha'c := uqCl_tow hQ (hΩN.trans hNx') hy (fun z hz => by
      exact ((veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 hz)).trans_lt hNx') hh hgx h2
    exact UgC.phi ha'c hx

/-- **`φ(a' + 1, 0)` with `a' ≥ Ω₂`**: the tower `φ(a', ·)` above `1`. -/
theorem uqMA_zero {a' : Ordinal.{0}} (ha'H : a' ∈ cdHull S l) (ha' : Om (1 + 1) ≤ a')
    (hEG : veblen (a' + 1) 0 < ugY S) : UqMA S l (veblen (a' + 1) 0) := by
  set E := veblen (a' + 1) 0 with hE_def
  have ha2 : Om (1 + 1) < a' + 1 := ha'.trans_lt (lt_add_one a')
  have ha'0 : a' ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans_le ha').ne'
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have haH : a' + 1 ∈ cdHull S l := CSet.succ_mem ha'H
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have h1E : (1 : Ordinal.{0}) < E := Rv.rvLim_one_lt hElim
  have hGE : veblen (Om (1 + 1)) 1 < E := udG_lt ha2
  have ha1G : a' + 1 < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hTa : ugTh S l (a' + 1) = ugTh S l a' + 1 := ugSucc hl hX ha'H ha1G
  have hT1 : ugTh S l 1 = 1 := by rw [uqThCode hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX]
  have hTa0 : ugTh S l a' ≠ 0 :=
    (ugPos hl hX ha'H (pos_iff_ne_zero.2 ha'0) ((lt_add_one a').trans ha1G)).ne'
  have hTE : ugTh S l E = veblen (ugTh S l a' + 1) 0 := by
    rw [uqVeb hl hX haH (CSet.zero_mem _ _) ha0 hGE.le hEG, hTa, ugTh_zero]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  have hlt : ∀ x, x < E → veblen a' x < E := fun x hx => by
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hx
      _ = E := hfix
  have hnfp : ∀ c : Ordinal.{0}, c ≠ 0 → veblen (c + 1) 0 = nfp (veblen c) 1 := fun c hc0 => by
    rw [veblen_add_one, deriv_zero_right]
    exact udNfp01 (isNormal_veblen c) (Order.one_le_iff_pos.2 veblen_pos)
  refine uqMA_towB hl hX (veblen a') (veblen a') (veblen (ugTh S l a')) (veblen (ugTh S l a')) hEG
    (CSet.one_mem _ _) le_rfl h1E (veblen_right_strictMono a').monotone (fun x => le_rfl)
    (hnfp a' ha'0) (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, hT1]; exact hnfp _ hTa0
  · intro x hxH _ hxE
    exact ⟨CSet.phi_mem ha'H hxH, hlt x hxE, right_le_veblen _ _⟩
  · intro x hxH h1x hxE
    exact uqVeb hl hX ha'H hxH ha'0 (udG_le ha' h1x) ((hlt x hxE).trans hEG)
  · intro Q hQ _ _ _ _
    exact UgC.small (gg_one_lt_of_SC hQ)
  · intro Q hQ x h hh h1x hgx h2 hx
    have hΩ : Om (1 + 1) < veblen a' x := tgOm_lt_G.trans_le (udG_le ha' h1x)
    have ha'c := uqCl_tow hQ hΩ veblen_pos (fun z hz => absurd hz (not_lt.2 zero_le)) hh hgx h2
    exact UgC.phi ha'c hx

/-- **`φ(a, y' + 1)`, `a > Ω₂` a limit with countable members `m`: the members `φ(m, N + 1)`.** -/
theorem uqMA_levLimH {a y' : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hy'H : y' ∈ cdHull S l) (hEG : veblen a (y' + 1) < ugY S) (hA : UqMA S l a) :
    UqMA S l (veblen a (y' + 1)) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  set E := veblen a (y' + 1) with hE_def
  set N := veblen a y' with hN_def
  have ha0 : a ≠ 0 := hlim.ne_bot
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hN1E : N + 1 < E := (taVeb_lim ha0).add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 < N := udG_lt hΩa
  have hΩN : Om (1 + 1) < N := tgOm_lt_G.trans hGN
  have haG : a < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEG
  have hTE : ugTh S l E = veblen (ugTh S l a) (ugTh S l y' + 1) := by
    rw [uqVeb hl hX haH (CSet.succ_mem hy'H) ha0 (hGN.trans hNE).le hEG, ugSucc hl hX hy'H hy1G]
  have hTN : ugTh S l N = veblen (ugTh S l a) (ugTh S l y') := uqVeb hl hX haH hy'H ha0 hGN.le (hNE.trans hEG)
  have hmE : ∀ m, m < a → veblen m (N + 1) < E := fun m hm => by
    calc veblen m (N + 1) < veblen m E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hm _
  have hTm : ∀ m, Mem m → ugTh S l (veblen m (N + 1)) = veblen (ugTh S l m) (ugTh S l N + 1) := fun m hm => by
    obtain ⟨hmH, hm1, hma⟩ := hdat m hm
    rw [uqVeb hl hX hmH (CSet.succ_mem hNH) (zero_lt_one.trans_le hm1).ne'
      (hGN.le.trans (le_self_add.trans (right_le_veblen _ _))) ((hmE m hma).trans hEG),
      ugSucc hl hX hNH (hN1E.trans hEG)]
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = veblen m (N + 1), ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    obtain ⟨hmH, -, hma⟩ := hdat m hm
    exact ⟨CSet.phi_mem hmH (CSet.succ_mem hNH), Order.one_le_iff_pos.2 veblen_pos, hmE m hma⟩
  · intro y0 hy0H hy0
    obtain ⟨c', hc'H, hc'a, hyc'⟩ := tdHull_levDec hlim y0 hy0H hy0
    obtain ⟨m, hm, hc'm⟩ := hA1 c' hc'H hc'a
    exact ⟨_, ⟨m, hm, rfl⟩, hyc'.trans_le (veblen_left_monotone _ hc'm.le)⟩
  · intro w hw
    rw [hTE] at hw
    obtain ⟨d, hd, hwd⟩ := taVeb_lim_cof (uqLimT hl hX a haH hlim haG) hw
    rw [← hTN] at hwd
    obtain ⟨m, hm, hdm⟩ := hA2 d hd
    exact ⟨_, ⟨m, hm, rfl⟩, by rw [hTm m hm]; exact hwd.trans_le (veblen_left_monotone _ hdm.le)⟩
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    have hNh : N < h := (lt_add_one N).trans_le ((right_le_veblen m (N + 1)).trans h1)
    have hNc := uqCl_N hQ hΩN hh hNh h2
    have hΩm : Om (1 + 1) < veblen m (N + 1) := hΩN.trans ((lt_add_one N).trans_le (right_le_veblen _ _))
    obtain ⟨p, q, hp, hmp, hq1, hq2⟩ := uqCl_levGe hΩm h hh h1
    have hpa : p ≤ a :=
      udLev_le ((lt_add_one N).trans_le ((right_le_veblen m (N + 1)).trans hq1)) (hq2.trans h2)
    exact UgC.phi (hA3 Q hQ m p hm hmp hpa hp) (UgC.add hNc (UgC.small (gg_one_lt_of_SC hQ)))

/-- **`φ(a, y' + 1)`, `a > Ω₂` a limit with members `M c` indexed by the codes: the members `φ(M c, N + 1)`.** -/
theorem uqMB_levLimH {a y' : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hy'H : y' ∈ cdHull S l) (hEG : veblen a (y' + 1) < ugY S) (hB : UqMB S l a) :
    UqMB S l (veblen a (y' + 1)) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen a (y' + 1) with hE_def
  set N := veblen a y' with hN_def
  have ha0 : a ≠ 0 := hlim.ne_bot
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hN1E : N + 1 < E := (taVeb_lim ha0).add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 < N := udG_lt hΩa
  have hΩN : Om (1 + 1) < N := tgOm_lt_G.trans hGN
  have haG : a < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEG
  have hTlim := uqLimT hl hX a haH hlim haG
  have hTa0 : ugTh S l a ≠ 0 := hTlim.ne_bot
  have hTE : ugTh S l E = veblen (ugTh S l a) (ugTh S l y' + 1) := by
    rw [uqVeb hl hX haH (CSet.succ_mem hy'H) ha0 (hGN.trans hNE).le hEG, ugSucc hl hX hy'H hy1G]
  have hTN : ugTh S l N = veblen (ugTh S l a) (ugTh S l y') := uqVeb hl hX haH hy'H ha0 hGN.le (hNE.trans hEG)
  have hTN1 : ugTh S l N + 1 < ugTh S l E := by
    rw [hTE, hTN]; exact (taVeb_lim hTa0).add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one _))
  have hmE : ∀ m, m < a → veblen m (N + 1) < E := fun m hm => by
    calc veblen m (N + 1) < veblen m E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hm _
  have hown : ∀ Q, SC Q → ∀ m h, UgC S (1 + 1) Q h → veblen m (N + 1) ≤ h → h ≤ E →
      UgC S (1 + 1) Q (N + 1) ∧ ∃ p, UgC S (1 + 1) Q p ∧ m ≤ p ∧ p ≤ a := by
    intro Q hQ m h hh h1 h2
    have hNm : N < veblen m (N + 1) := (lt_add_one N).trans_le (right_le_veblen _ _)
    have hNc := uqCl_N hQ hΩN hh (hNm.trans_le h1) h2
    obtain ⟨p, q, hp, hmp, hq1, hq2⟩ := uqCl_levGe (hΩN.trans hNm) h hh h1
    exact ⟨UgC.add hNc (UgC.small (gg_one_lt_of_SC hQ)), p, hp, hmp,
      udLev_le (hNm.trans_le hq1) (hq2.trans h2)⟩
  refine ⟨fun c => veblen (M c) (N + 1), fun v => veblen (Mh v) (ugTh S l N + 1),
    fun x z h => veblen_left_monotone _ (hM h), fun x z h => veblen_left_monotone _ (hMh h), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, hM1, hMa, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    refine ⟨CSet.phi_mem hMH (CSet.succ_mem hNH), Order.one_le_iff_pos.2 veblen_pos, hmE _ hMa, ?_, ?_⟩
    · rw [uqVeb hl hX hMH (CSet.succ_mem hNH) (zero_lt_one.trans_le hM1).ne'
        (hGN.le.trans (le_self_add.trans (right_le_veblen _ _))) ((hmE _ hMa).trans hEG),
        ugSucc hl hX hNH (hN1E.trans hEG), hTM]
    · calc veblen (Mh (gxTh (upsilon l) (ldAtR S l) c)) (ugTh S l N + 1)
          < veblen (Mh (gxTh (upsilon l) (ldAtR S l) c)) (ugTh S l E) := (veblen_lt_veblen_iff_right).2 hTN1
        _ = ugTh S l E := by rw [hTE]; exact veblen_veblen_of_lt hMhT _
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := uqCl_levDec hQ ugTwo_ne hlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB1 Q hQ hQ1 c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ hc'M.le)⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := uqCl_levDec hQ one_ne_zero hTlim w hw hwE
    rw [← hTN] at hwc'
    obtain ⟨c'', hc''Q, hc'M⟩ := hB2 Q hQ c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ hc'M.le)⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    obtain ⟨hN1c, p, hp, hmp, hpa⟩ := hown Q hQ (M c) h hh h1 h2
    exact UgC.phi (hB3 Q hQ c p hc1 hcQ hmp hpa hp) hN1c

/-- **`φ(a, 0)`, `a > Ω₂` a limit with countable members: the members `φ(m, 0)`, `m > Ω₂`.** -/
theorem uqMA_lev0 {a : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hEG : veblen a 0 < ugY S) (hA : UqMA S l a) : UqMA S l (veblen a 0) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  have ha0 : a ≠ 0 := hlim.ne_bot
  have haG : a < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hΩH : Om (1 + 1) ∈ cdHull S l := mxOm2_mem _ _
  have hTE : ugTh S l (veblen a 0) = veblen (ugTh S l a) 0 := by
    rw [uqVeb hl hX haH (CSet.zero_mem _ _) ha0 (udG_lt hΩa).le hEG, ugTh_zero]
  have hmE : ∀ m, m < a → veblen m 0 < veblen a 0 := fun m hm => veblen_zero_strictMono hm
  have hTm : ∀ m, Mem m → Om (1 + 1) < m → ugTh S l (veblen m 0) = veblen (ugTh S l m) 0 := fun m hm hΩm => by
    obtain ⟨hmH, hm1, hma⟩ := hdat m hm
    rw [uqVeb hl hX hmH (CSet.zero_mem _ _) (zero_lt_one.trans_le hm1).ne' (udG_lt hΩm).le
      ((hmE m hma).trans hEG), ugTh_zero]
  obtain ⟨m0, hm0, hΩm0⟩ := hA1 _ hΩH hΩa
  refine ⟨fun m' => ∃ m, Mem m ∧ Om (1 + 1) < m ∧ m' = veblen m 0, ?_, ⟨_, m0, hm0, hΩm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, -, rfl⟩
    obtain ⟨hmH, -, hma⟩ := hdat m hm
    exact ⟨CSet.phi_mem hmH (CSet.zero_mem _ _), Order.one_le_iff_pos.2 veblen_pos, hmE m hma⟩
  · intro y0 hy0H hy0
    obtain ⟨c', hc'H, hc'a, hyc'⟩ := udHull_levDec0 hlim y0 hy0H hy0
    have hmaxH : max c' (Om (1 + 1)) ∈ cdHull S l := by
      rcases le_total c' (Om (1 + 1)) with h | h
      · rw [max_eq_right h]; exact hΩH
      · rw [max_eq_left h]; exact hc'H
    obtain ⟨m, hm, hmm⟩ := hA1 _ hmaxH (max_lt hc'a hΩa)
    exact ⟨_, ⟨m, hm, (le_max_right _ _).trans_lt hmm, rfl⟩,
      hyc'.trans_le (veblen_left_monotone _ ((le_max_left _ _).trans hmm.le))⟩
  · intro w hw
    rw [hTE] at hw
    have hTlim := uqLimT hl hX a haH hlim haG
    obtain ⟨d, hd, hwd⟩ := udLev0 hTlim hw
    have hTΩ : ugTh S l (Om (1 + 1)) < ugTh S l a := ugLt hl hX hΩH haH haG hΩa
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hd hTΩ)
    have hΩm : Om (1 + 1) < m := by
      by_contra hc
      push Not at hc
      exact absurd ((le_max_right _ _).trans_lt hmm) (not_lt.2 (ugLe hl hX (hdat m hm).1 hΩH
        uqW_lt_Y hc))
    refine ⟨_, ⟨m, hm, hΩm, rfl⟩, ?_⟩
    rw [hTm m hm hΩm]
    exact hwd.trans_le (veblen_left_monotone _ ((le_max_left _ _).trans hmm.le))
  · rintro Q hQ m' h ⟨m, hm, hΩm, rfl⟩ h1 h2 hh
    obtain ⟨p, hp, hmp, hpa⟩ := uqOwn0 hΩm hh h1 h2
    exact UgC.phi (hA3 Q hQ m p hm hmp hpa hp) (UgC.zero hQ.1)

/-- **`φ(a, 0)`, `a > Ω₂` a limit with members `M c` indexed by the codes: the members `φ(max (M c) (Ω₂+1), 0)`.** -/
theorem uqMB_lev0 {a : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hEG : veblen a 0 < ugY S) (hB : UqMB S l a) : UqMB S l (veblen a 0) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have ha0 : a ≠ 0 := hlim.ne_bot
  have haG : a < ugY S := (left_le_veblen _ _).trans_lt hEG
  have hΩH : Om (1 + 1) ∈ cdHull S l := mxOm2_mem _ _
  have hΩ1H : Om (1 + 1) + 1 ∈ cdHull S l := CSet.succ_mem hΩH
  have hΩ1a : Om (1 + 1) + 1 < a := hlim.add_one_lt hΩa
  have hΩ1G : Om (1 + 1) + 1 < ugY S := hΩ1a.trans haG
  have hTlim := uqLimT hl hX a haH hlim haG
  set K := ugTh S l (Om (1 + 1)) with hK
  have hTΩ1 : ugTh S l (Om (1 + 1) + 1) = K + 1 := ugSucc hl hX hΩH hΩ1G
  have hK1a : K + 1 < ugTh S l a := by rw [← hTΩ1]; exact ugLt hl hX hΩ1H haH haG hΩ1a
  have hTE : ugTh S l (veblen a 0) = veblen (ugTh S l a) 0 := by
    rw [uqVeb hl hX haH (CSet.zero_mem _ _) ha0 (udG_lt hΩa).le hEG, ugTh_zero]
  refine ⟨fun c => veblen (max (M c) (Om (1 + 1) + 1)) 0, fun v => veblen (max (Mh v) (K + 1)) 0,
    fun x z h => veblen_left_monotone _ (max_le_max (hM h) le_rfl),
    fun x z h => veblen_left_monotone _ (max_le_max (hMh h) le_rfl), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, -, hMa, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hmxH : max (M c) (Om (1 + 1) + 1) ∈ cdHull S l := by
      rcases le_total (M c) (Om (1 + 1) + 1) with h | h
      · rw [max_eq_right h]; exact hΩ1H
      · rw [max_eq_left h]; exact hMH
    have hmxa : max (M c) (Om (1 + 1) + 1) < a := max_lt hMa hΩ1a
    have hΩmx : Om (1 + 1) < max (M c) (Om (1 + 1) + 1) := (lt_add_one _).trans_le (le_max_right _ _)
    have hlt : veblen (max (M c) (Om (1 + 1) + 1)) 0 < veblen a 0 := veblen_zero_strictMono hmxa
    refine ⟨CSet.phi_mem hmxH (CSet.zero_mem _ _), Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [uqVeb hl hX hmxH (CSet.zero_mem _ _) (zero_lt_one.trans_le (le_add_self.trans (le_max_right _ _))).ne'
        (udG_lt hΩmx).le (hlt.trans hEG), ugTh_zero, uqTh_max hl hX hMH hΩ1H (hMa.trans haG) hΩ1G, hTM, hTΩ1]
    · rw [hTE]; exact veblen_zero_strictMono (max_lt hMhT hK1a)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := uqCl_levDec0 hQ ugTwo_ne hlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB1 Q hQ hQ1 c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ (hc'M.le.trans (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := uqCl_levDec0 hQ one_ne_zero hTlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB2 Q hQ c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ (hc'M.le.trans (le_max_left _ _)))⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have hΩmx : Om (1 + 1) < max (M c) (Om (1 + 1) + 1) := (lt_add_one _).trans_le (le_max_right _ _)
    obtain ⟨p, hp, hmp, hpa⟩ := uqOwn0 hΩmx hh h1 h2
    refine UgC.phi ?_ (UgC.zero hQ.1)
    rcases le_total (M c) (Om (1 + 1) + 1) with hle | hle
    · rw [max_eq_right hle]; exact UgC.add UgC.om (UgC.small (gg_one_lt_of_SC hQ))
    · rw [max_eq_left hle] at hmp ⊢
      exact hB3 Q hQ c p hc1 hcQ hmp hpa hp

/-- **`φ(a, y)`, `a > Ω₂`, `y` a limit with countable members: the members `φ(a, m)`, `m > t`.** -/
theorem uqMA_argLimH {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hyH : y ∈ cdHull S l)
    (hylim : IsSuccLimit y) (hyE : y < veblen a y) (hEG : veblen a y < ugY S) (hA : UqMA S l y) :
    UqMA S l (veblen a y) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  obtain ⟨t, htH, hty, hnf, -⟩ := uqThr haH hyH hΩa hyE hylim
  have ha0 : a ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hΩa).ne'
  have hyG : y < ugY S := hyE.trans hEG
  have hTE : ugTh S l (veblen a y) = veblen (ugTh S l a) (ugTh S l y) :=
    uqVeb hl hX haH hyH ha0 (udG_lt hΩa).le hEG
  have hmE : ∀ m, m < y → veblen a m < veblen a y := fun m hm => (veblen_lt_veblen_iff_right).2 hm
  obtain ⟨m0, hm0, htm0⟩ := hA1 t htH hty
  refine ⟨fun m' => ∃ m, Mem m ∧ t < m ∧ m' = veblen a m, ?_, ⟨_, m0, hm0, htm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, -, rfl⟩
    obtain ⟨hmH, -, hmy⟩ := hdat m hm
    exact ⟨CSet.phi_mem haH hmH, Order.one_le_iff_pos.2 veblen_pos, hmE m hmy⟩
  · intro y0 hy0H hy0
    by_cases h0 : veblen a 0 ≤ y0
    swap
    · push Not at h0
      exact ⟨_, ⟨m0, hm0, htm0, rfl⟩, h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le)⟩
    obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hy0H h0
    have huy : u < y := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hy0)
    have hmaxH : max u t ∈ cdHull S l := by
      rcases le_total u t with h | h
      · rw [max_eq_right h]; exact htH
      · rw [max_eq_left h]; exact huH
    obtain ⟨m, hm, hmm⟩ := hA1 _ hmaxH (max_lt huy hty)
    refine ⟨_, ⟨m, hm, (le_max_right u t).trans_lt hmm, rfl⟩, hu2.trans_le ((veblen_le_veblen_iff_right).2 ?_)⟩
    exact Order.add_one_le_of_lt ((le_max_left u t).trans_lt hmm)
  · intro w hw
    rw [hTE] at hw
    have hTlim : IsSuccLimit (ugTh S l y) := uqLimT hl hX y hyH hylim hyG
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    have hTty : ugTh S l t < ugTh S l y := ugLt hl hX htH hyH hyG hty
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hu' hTty)
    have htm : t < m := by
      by_contra hc
      push Not at hc
      exact absurd ((le_max_right _ _).trans_lt hmm)
        (not_lt.2 (ugLe hl hX (hdat m hm).1 htH (hty.trans hyG) hc))
    refine ⟨_, ⟨m, hm, htm, rfl⟩, ?_⟩
    rw [uqVeb hl hX haH (hdat m hm).1 ha0 (udG_lt hΩa).le ((hmE m (hdat m hm).2.2).trans hEG)]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 ((le_max_left _ _).trans_lt hmm))
  · rintro Q hQ m' h ⟨m, hm, htm, rfl⟩ h1 h2 hh
    obtain ⟨hac, u, hu, hmu, huy⟩ :=
      uqOwnArg hQ hΩa (fun v hmv hvy => hnf v (htm.trans_le hmv) hvy) hh h1 h2
    exact UgC.phi hac (hA3 Q hQ m u hm hmu huy hu)

/-- **`φ(a, y)`, `a > Ω₂`, `y` a limit with members `M c` indexed by the codes: the members
`φ(a, max (M c) (t + 1))`.** -/
theorem uqMB_argLimH {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hyH : y ∈ cdHull S l)
    (hylim : IsSuccLimit y) (hyE : y < veblen a y) (hEG : veblen a y < ugY S) (hB : UqMB S l y) :
    UqMB S l (veblen a y) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  obtain ⟨t, htH, hty, hnf, htc⟩ := uqThr haH hyH hΩa hyE hylim
  have ha0 : a ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hΩa).ne'
  have hyG : y < ugY S := hyE.trans hEG
  have ht1H : t + 1 ∈ cdHull S l := CSet.succ_mem htH
  have ht1y : t + 1 < y := hylim.add_one_lt hty
  have ht1G : t + 1 < ugY S := ht1y.trans hyG
  have hTlim : IsSuccLimit (ugTh S l y) := uqLimT hl hX y hyH hylim hyG
  set Tt := ugTh S l t with hTt
  have hTt1 : ugTh S l (t + 1) = Tt + 1 := ugSucc hl hX htH ht1G
  have hTt1y : Tt + 1 < ugTh S l y := by rw [← hTt1]; exact ugLt hl hX ht1H hyH hyG ht1y
  have hTE : ugTh S l (veblen a y) = veblen (ugTh S l a) (ugTh S l y) :=
    uqVeb hl hX haH hyH ha0 (udG_lt hΩa).le hEG
  have hΘaO : ugTh S l a ≠ 0 := (ugPos hl hX haH (pos_iff_ne_zero.2 ha0) ((left_le_veblen a y).trans_lt hEG)).ne'
  refine ⟨fun c => veblen a (max (M c) (t + 1)), fun v => veblen (ugTh S l a) (max (Mh v) (Tt + 1)),
    fun x z h => (veblen_le_veblen_iff_right).2 (max_le_max (hM h) le_rfl),
    fun x z h => (veblen_le_veblen_iff_right).2 (max_le_max (hMh h) le_rfl), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, -, hMy, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hmxH : max (M c) (t + 1) ∈ cdHull S l := by
      rcases le_total (M c) (t + 1) with h | h
      · rw [max_eq_right h]; exact ht1H
      · rw [max_eq_left h]; exact hMH
    have hmxy : max (M c) (t + 1) < y := max_lt hMy ht1y
    have hlt : veblen a (max (M c) (t + 1)) < veblen a y := (veblen_lt_veblen_iff_right).2 hmxy
    refine ⟨CSet.phi_mem haH hmxH, Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [uqVeb hl hX haH hmxH ha0 (udG_lt hΩa).le (hlt.trans hEG),
        uqTh_max hl hX hMH ht1H (hMy.trans hyG) ht1G, hTM, hTt1]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 (max_lt hMhT hTt1y)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u, hu, huy, hwu⟩ := uqCl_decA hQ ugTwo_ne hylim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u, hu, huy, hwu⟩ := uqCl_decA hQ one_ne_zero hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have htm : t < max (M c) (t + 1) := (lt_add_one t).trans_le (le_max_right _ _)
    obtain ⟨hac, u, hu, hmu, huy⟩ :=
      uqOwnArg hQ hΩa (fun v hmv hvy => hnf v (htm.trans_le hmv) hvy) hh h1 h2
    refine UgC.phi hac ?_
    rcases le_total (M c) (t + 1) with hle | hle
    · change veblen a (max (M c) (t + 1)) ≤ h at h1
      rw [max_eq_right hle] at h1 ⊢
      exact htc Q hQ h hh h1 h2
    · rw [max_eq_left hle] at hmu ⊢
      exact hB3 Q hQ c u hc1 hcQ hmu huy hu

/-- **Every node `φ(a, y) < Γ₂` with a level `a > Ω₂` has a member system** (given those of `a` and `y` when they
are limits). -/
theorem uqNodeHi {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hΩa : Om (1 + 1) < a)
    (hyE : y < veblen a y) (hEG : veblen a y < ugY S)
    (IHa : IsSuccLimit a → UqMA S l a ∨ UqMB S l a) (IHy : IsSuccLimit y → UqMA S l y ∨ UqMB S l y) :
    UqMA S l (veblen a y) ∨ UqMB S l (veblen a y) := by
  rcases zero_or_succ_or_isSuccLimit y with hy0 | ⟨y', hy'⟩ | hyl
  rotate_left
  · -- a successor argument
    rw [succ_eq_add_one] at hy'
    subst hy'
    have hy'H : y' ∈ cdHull S l := mem_of_add_one_mem hyH
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at hΩa; exact absurd hΩa (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      exact Or.inl (uqMA_succ hl hX (mem_of_add_one_mem haH) (Order.lt_add_one_iff.1 hΩa) hy'H hEG)
    · rcases IHa hal with hA | hB
      · exact Or.inl (uqMA_levLimH hl hX haH hΩa hal hy'H hEG hA)
      · exact Or.inr (uqMB_levLimH hl hX haH hΩa hal hy'H hEG hB)
  · -- a limit argument
    rcases IHy hyl with hA | hB
    · exact Or.inl (uqMA_argLimH hl hX haH hΩa hyH hyl hyE hEG hA)
    · exact Or.inr (uqMB_argLimH hl hX haH hΩa hyH hyl hyE hEG hB)
  · -- the argument `0`
    subst hy0
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at hΩa; exact absurd hΩa (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      exact Or.inl (uqMA_zero hl hX (mem_of_add_one_mem haH) (Order.lt_add_one_iff.1 hΩa) hEG)
    · rcases IHa hal with hA | hB
      · exact Or.inl (uqMA_lev0 hl hX haH hΩa hal hEG hA)
      · exact Or.inr (uqMB_lev0 hl hX haH hΩa hal hEG hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
