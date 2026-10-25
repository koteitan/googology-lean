import Googology.Trans.PoR.InaccPsi.R2.UdGam

/-!
# Member systems of the nodes `φ(a' + 1, y)` with a level `a' + 1 > Ω₂`: the towers `φ(a', ·)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `Γ₂ = Ua.uaGam`, member systems
`Ua.UaMA`, `Ua.UaMB`.

* `udG_lt`, `udG_le` (`G ≤ φ(c, z)` for `c > Ω₂`, resp. `c ≥ Ω₂`, `z ≥ 1`), `udNfp01` (`nfp f 0 = nfp f 1`);
* `udMA_tow` (**a tower from any start `b ≥ 1` dominating a normal fixed point gives countable members**;
  `Ua.uaMA_tow` is the start `N + 1`);
* `udMA_succ` (**`φ(a' + 1, y' + 1)`, `a' ≥ Ω₂`: the tower `φ(a', ·)` above `N + 1`, `N = φ(a' + 1, y')`**; the own
  transfer by `Ud.udCl_N` and `Ud.udCl_tow`), `udMA_zero` (**`φ(a' + 1, 0)`, `a' ≥ Ω₂`: the tower `φ(a', ·)` above
  `1`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu
  Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- `G < φ(c, z)` for a level `c > Ω₂`. -/
theorem udG_lt {c z : Ordinal.{0}} (hc : Om (1 + 1) < c) : veblen (Om (1 + 1)) 1 < veblen c z := by
  refine (veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hc, ?_⟩))).trans_le (veblen_le_veblen_iff_right.2 zero_le)
  exact (gg_one_lt_of_SC ldOm2_SC).trans (hc.trans_le (left_le_veblen c 0))

/-- `G ≤ φ(c, z)` for a level `c ≥ Ω₂` and `z ≥ 1`. -/
theorem udG_le {c z : Ordinal.{0}} (hc : Om (1 + 1) ≤ c) (hz : 1 ≤ z) : veblen (Om (1 + 1)) 1 ≤ veblen c z := by
  rcases hc.lt_or_eq with h | rfl
  · exact (udG_lt h).le
  · exact veblen_le_veblen_iff_right.2 hz

/-- `nfp f 0 = nfp f 1` for a normal `f` with `1 ≤ f 0`. -/
theorem udNfp01 {f : Ordinal.{0} → Ordinal.{0}} (hf : IsNormal f) (h : 1 ≤ f 0) : nfp f 0 = nfp f 1 := by
  refine le_antisymm (nfp_monotone hf.monotone zero_le) (nfp_le_fp hf.monotone ?_ (nfp_fp hf 0).le)
  exact h.trans (iterate_le_nfp f 0 1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A tower from a start `b ≥ 1` dominating a normal fixed point gives countable members.** -/
theorem udMA_tow {E b : Ordinal.{0}} (f g fh gh : Ordinal.{0} → Ordinal.{0})
    (hEG : E < uaGam) (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b) (hbE : b < E)
    (hfm : Monotone f) (hfg : ∀ x, f x ≤ g x) (hE : E = nfp f b)
    (hfhm : Monotone fh) (hfgh : ∀ x, fh x ≤ gh x) (hEh : uaTh S l E = nfp fh (uaTh S l b))
    (hg : ∀ x, x ∈ cdHull S l → b ≤ x → x < E → g x ∈ cdHull S l ∧ g x < E ∧ x ≤ g x)
    (hTg : ∀ x, x ∈ cdHull S l → b ≤ x → x < E → uaTh S l (g x) = gh (uaTh S l x))
    (hcb : ∀ Q, SC Q → ∀ h, LeCl (Om (1 + 1)) Q h → b ≤ h → h ≤ E → LeCl (Om (1 + 1)) Q b)
    (hcg : ∀ Q, SC Q → ∀ x h, LeCl (Om (1 + 1)) Q h → b ≤ x → g x ≤ h → h ≤ E →
      LeCl (Om (1 + 1)) Q x → LeCl (Om (1 + 1)) Q (g x)) :
    UaMA S l E := by
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
    obtain ⟨j, hj⟩ := taTw_cof hfhm hfgh hw (fun j => uaTh S l (u j)) le_rfl
      (fun j => by
        show uaTh S l (u (j + 1)) = gh (uaTh S l (u j))
        rw [hus]; exact hTg _ (hu j).1 (hu j).2.2 (hu j).2.1)
    refine ⟨_, ⟨j, rfl⟩, hj.trans_le ?_⟩
    exact uaLe hl hX (hu j).1 (hu (j + 1)).1 ((hu (j + 1)).2.1.trans hEG) (hstep j)
  · rintro Q hQ m h ⟨j, rfl⟩ h1 h2 hh
    have hbc : LeCl (Om (1 + 1)) Q b := hcb Q hQ h hh ((hu (j + 1)).2.2.trans h1) h2
    have key : ∀ i, i ≤ j + 1 → LeCl (Om (1 + 1)) Q (u i) := by
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
theorem udMA_succ {a' y' : Ordinal.{0}} (ha'H : a' ∈ cdHull S l) (ha' : Om (1 + 1) ≤ a')
    (hy'H : y' ∈ cdHull S l) (hEG : veblen (a' + 1) (y' + 1) < uaGam) :
    UaMA S l (veblen (a' + 1) (y' + 1)) := by
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
  have hNG : N < uaGam := hNE.trans hEG
  have ha1G : a' + 1 < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTa : uaTh S l (a' + 1) = uaTh S l a' + 1 := uaSucc hl hX ha'H ha1G
  have hTE : uaTh S l E = veblen (uaTh S l a' + 1) (uaTh S l y' + 1) := by
    rw [uaVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEG, hTa, uaSucc hl hX hy'H hy1G]
  have hTN : uaTh S l N = veblen (uaTh S l a' + 1) (uaTh S l y') := by
    rw [uaVeb hl hX haH hy'H ha0 hGN.le hNG, hTa]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  have hlt : ∀ x, x < E → veblen a' x < E := fun x hx => by
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hx
      _ = E := hfix
  refine udMA_tow hl hX (veblen a') (veblen a') (veblen (uaTh S l a')) (veblen (uaTh S l a')) hEG
    (CSet.succ_mem hNH) le_add_self hN1E (veblen_right_strictMono a').monotone (fun x => le_rfl)
    (taVeb_succ a' y') (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, uaSucc hl hX hNH (hN1E.trans hEG), hTN, taVeb_succ]
  · intro x hxH _ hxE
    exact ⟨CSet.phi_mem ha'H hxH, hlt x hxE, right_le_veblen _ _⟩
  · intro x hxH hNx hxE
    have hvG : veblen (Om (1 + 1)) 1 ≤ veblen a' x :=
      (hGN.le.trans ((le_self_add.trans hNx).trans (right_le_veblen _ _)))
    exact uaVeb hl hX ha'H hxH ha'0 hvG ((hlt x hxE).trans hEG)
  · intro Q hQ h hh h1 h2
    exact LeCl.add (udCl_N hQ hΩN hh ((lt_add_one N).trans_le h1) h2) (LeCl.small (gg_one_lt_of_SC hQ))
  · intro Q hQ x h hh hNx hgx h2 hx
    have hNx' : N < veblen a' x := (lt_add_one N).trans_le (hNx.trans (right_le_veblen _ _))
    have hy : y' + 1 < E := hElim.add_one_lt ((right_le_veblen _ _).trans_lt hNE)
    have ha'c := udCl_tow hQ (hΩN.trans hNx') hy (fun z hz => by
      exact ((veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 hz)).trans_lt hNx') hh hgx h2
    exact LeCl.phi ha'c hx

/-- **`φ(a' + 1, 0)` with `a' ≥ Ω₂`**: the tower `φ(a', ·)` above `1`. -/
theorem udMA_zero {a' : Ordinal.{0}} (ha'H : a' ∈ cdHull S l) (ha' : Om (1 + 1) ≤ a')
    (hEG : veblen (a' + 1) 0 < uaGam) : UaMA S l (veblen (a' + 1) 0) := by
  set E := veblen (a' + 1) 0 with hE_def
  have ha2 : Om (1 + 1) < a' + 1 := ha'.trans_lt (lt_add_one a')
  have ha'0 : a' ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans_le ha').ne'
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have haH : a' + 1 ∈ cdHull S l := CSet.succ_mem ha'H
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have h1E : (1 : Ordinal.{0}) < E := Rv.rvLim_one_lt hElim
  have hGE : veblen (Om (1 + 1)) 1 < E := udG_lt ha2
  have ha1G : a' + 1 < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hTa : uaTh S l (a' + 1) = uaTh S l a' + 1 := uaSucc hl hX ha'H ha1G
  have hT1 : uaTh S l 1 = 1 := by rw [uaThCode hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX]
  have hTa0 : uaTh S l a' ≠ 0 :=
    (uaPos hl hX ha'H (pos_iff_ne_zero.2 ha'0) ((lt_add_one a').trans ha1G)).ne'
  have hTE : uaTh S l E = veblen (uaTh S l a' + 1) 0 := by
    rw [uaVeb hl hX haH (CSet.zero_mem _ _) ha0 hGE.le hEG, hTa, uaTh_zero]
  have hfix : veblen a' E = E := veblen_veblen_of_lt (lt_add_one a') _
  have hlt : ∀ x, x < E → veblen a' x < E := fun x hx => by
    calc veblen a' x < veblen a' E := (veblen_lt_veblen_iff_right).2 hx
      _ = E := hfix
  have hnfp : ∀ c : Ordinal.{0}, c ≠ 0 → veblen (c + 1) 0 = nfp (veblen c) 1 := fun c hc0 => by
    rw [veblen_add_one, deriv_zero_right]
    exact udNfp01 (isNormal_veblen c) (Order.one_le_iff_pos.2 veblen_pos)
  refine udMA_tow hl hX (veblen a') (veblen a') (veblen (uaTh S l a')) (veblen (uaTh S l a')) hEG
    (CSet.one_mem _ _) le_rfl h1E (veblen_right_strictMono a').monotone (fun x => le_rfl)
    (hnfp a' ha'0) (veblen_right_strictMono _).monotone (fun x => le_rfl) ?_ ?_ ?_ ?_ ?_
  · rw [hTE, hT1]; exact hnfp _ hTa0
  · intro x hxH _ hxE
    exact ⟨CSet.phi_mem ha'H hxH, hlt x hxE, right_le_veblen _ _⟩
  · intro x hxH h1x hxE
    exact uaVeb hl hX ha'H hxH ha'0 (udG_le ha' h1x) ((hlt x hxE).trans hEG)
  · intro Q hQ _ _ _ _
    exact LeCl.small (gg_one_lt_of_SC hQ)
  · intro Q hQ x h hh h1x hgx h2 hx
    have hΩ : Om (1 + 1) < veblen a' x := tgOm_lt_G.trans_le (udG_le ha' h1x)
    have ha'c := udCl_tow hQ hΩ veblen_pos (fun z hz => absurd hz (not_lt.2 zero_le)) hh hgx h2
    exact LeCl.phi ha'c hx

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ud
