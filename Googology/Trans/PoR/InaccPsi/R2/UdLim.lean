import Googology.Trans.PoR.InaccPsi.R2.UdTow

/-!
# Member systems of the nodes `φ(a, y)` with a level `a > Ω₂`: limit levels and limit arguments

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `Γ₂ = Ua.uaGam`, `N = φ(a, y')`,
member systems `Ua.UaMA`, `Ua.UaMB`.  The members of a node at a limit level are **indexed by the members of the
level `a` itself** (its member system), so that the own transfer of the level gives a code.

* `udMA_levLim`, `udMB_levLim` (**`φ(a, y' + 1)`, `a > Ω₂` a limit: the members `φ(m, N + 1)` for the members `m`
  of `a`**; images `φ(T m, T N + 1)`);
* `udMA_lev0`, `udMB_lev0` (**`φ(a, 0)`, `a > Ω₂` a limit: the members `φ(m, 0)`, `m > Ω₂` a member of `a`**);
* `udThr` (**the threshold of a limit argument**: the last fixed point `t` of `φ(a, ·)` below `y`, with no fixed
  point in `(t, y]` and `t + 1` a code under every code in `[φ(a, t + 1), φ(a, y)]`);
* `udMA_argLim`, `udMB_argLim` (**`φ(a, y)`, `a > Ω₂`, `y` a limit: the members `φ(a, m)`, `m > t` a member of
  `y`**).

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

/-- A node `φ(p, q)` with `p > a` is not in `(φ(a, y'), φ(a, y' + 1)]`. -/
theorem udLev_le {a y' p q : Ordinal.{0}} (h1 : veblen a y' < veblen p q) (h2 : veblen p q ≤ veblen a (y' + 1)) :
    p ≤ a := by
  by_contra hc
  push Not at hc
  exact uaNoFix h1 h2 (veblen_veblen_of_lt hc q)

/-- A node `φ(p, q)` with `p > a` is not `≤ φ(a, 0)`. -/
theorem udLev_le0 {a p q : Ordinal.{0}} (h : veblen p q ≤ veblen a 0) : p ≤ a := by
  by_contra hc
  push Not at hc
  have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hc q
  rw [← hfix] at h
  exact absurd ((veblen_le_veblen_iff_right).1 h) (not_le.2 veblen_pos)

/-- **The threshold of a limit argument**: `t < y` in the closure with no fixed point of `φ(a, ·)` in `(t, y]`, and
`t + 1` a code under every code `h` with `φ(a, t + 1) ≤ h ≤ φ(a, y)`. -/
theorem udThr {A B a y : Ordinal.{0}} (haH : a ∈ S.CSet A B) (hyH : y ∈ S.CSet A B) (hΩ : Om (1 + 1) < a)
    (hy : y < veblen a y) (hylim : IsSuccLimit y) :
    ∃ t, t ∈ S.CSet A B ∧ t < y ∧ (∀ v, t < v → v ≤ y → veblen a v ≠ v) ∧
      (∀ Q, SC Q → ∀ h, LeCl (Om (1 + 1)) Q h → veblen a (t + 1) ≤ h → h ≤ veblen a y →
        LeCl (Om (1 + 1)) Q (t + 1)) := by
  rcases lt_or_ge y (veblen (a + 1) 0) with hy0 | hy0
  · refine ⟨0, CSet.zero_mem _ _, hylim.bot_lt, fun v _ hvy hfix => ?_, fun Q hQ _ _ _ _ => ?_⟩
    · obtain ⟨z, hz, -⟩ := udFix_lt hfix (hvy.trans_lt hy0)
      exact absurd hz (not_lt.2 zero_le)
    · rw [zero_add]; exact LeCl.small (gg_one_lt_of_SC hQ)
  obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hyH hy0
  set t := veblen (a + 1) u with ht
  have htfix : veblen a t = t := veblen_veblen_of_lt (lt_add_one a) u
  have hty : t < y := lt_of_le_of_ne hu1 fun e => absurd (e ▸ htfix) (ne_of_gt hy)
  have hΩt : Om (1 + 1) < t :=
    hΩ.trans_le ((le_self_add.trans (left_le_veblen (a + 1) 0)).trans ((veblen_le_veblen_iff_right).2 zero_le))
  refine ⟨t, CSet.phi_mem (CSet.succ_mem haH) huH, hty, fun v htv hvy hfix => ?_, fun Q hQ h hh h1 h2 => ?_⟩
  · obtain ⟨z, hz, hzv⟩ := udFix_lt hfix (hvy.trans_lt hu2)
    have : v ≤ t := by rw [← hzv]; exact (veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 hz)
    exact absurd htv (not_lt.2 this)
  · have hE : veblen a y < veblen (a + 1) (u + 1) := by
      calc veblen a y < veblen a (veblen (a + 1) (u + 1)) := (veblen_lt_veblen_iff_right).2 hu2
        _ = veblen (a + 1) (u + 1) := veblen_veblen_of_lt (lt_add_one a) _
    have htc : LeCl (Om (1 + 1)) Q t := udCl_N hQ hΩt hh
      ((lt_add_one t).trans_le ((right_le_veblen a (t + 1)).trans h1)) (h2.trans hE.le)
    exact LeCl.add htc (LeCl.small (gg_one_lt_of_SC hQ))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`φ(a, y' + 1)`, `a > Ω₂` a limit with countable members `m`: the members `φ(m, N + 1)`.** -/
theorem udMA_levLim {a y' : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hy'H : y' ∈ cdHull S l) (hEG : veblen a (y' + 1) < uaGam) (hA : UaMA S l a) :
    UaMA S l (veblen a (y' + 1)) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  set E := veblen a (y' + 1) with hE_def
  set N := veblen a y' with hN_def
  have ha0 : a ≠ 0 := hlim.ne_bot
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hN1E : N + 1 < E := (taVeb_lim ha0).add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 < N := udG_lt hΩa
  have hΩN : Om (1 + 1) < N := tgOm_lt_G.trans hGN
  have haG : a < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTE : uaTh S l E = veblen (uaTh S l a) (uaTh S l y' + 1) := by
    rw [uaVeb hl hX haH (CSet.succ_mem hy'H) ha0 (hGN.trans hNE).le hEG, uaSucc hl hX hy'H hy1G]
  have hTN : uaTh S l N = veblen (uaTh S l a) (uaTh S l y') := uaVeb hl hX haH hy'H ha0 hGN.le (hNE.trans hEG)
  have hmE : ∀ m, m < a → veblen m (N + 1) < E := fun m hm => by
    calc veblen m (N + 1) < veblen m E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hm _
  have hTm : ∀ m, Mem m → uaTh S l (veblen m (N + 1)) = veblen (uaTh S l m) (uaTh S l N + 1) := fun m hm => by
    obtain ⟨hmH, hm1, hma⟩ := hdat m hm
    rw [uaVeb hl hX hmH (CSet.succ_mem hNH) (zero_lt_one.trans_le hm1).ne'
      (hGN.le.trans (le_self_add.trans (right_le_veblen _ _))) ((hmE m hma).trans hEG),
      uaSucc hl hX hNH (hN1E.trans hEG)]
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
    obtain ⟨d, hd, hwd⟩ := taVeb_lim_cof (uaLimT hl hX a haH hlim haG) hw
    rw [← hTN] at hwd
    obtain ⟨m, hm, hdm⟩ := hA2 d hd
    exact ⟨_, ⟨m, hm, rfl⟩, by rw [hTm m hm]; exact hwd.trans_le (veblen_left_monotone _ hdm.le)⟩
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    have hNh : N < h := (lt_add_one N).trans_le ((right_le_veblen m (N + 1)).trans h1)
    have hNc := udCl_N hQ hΩN hh hNh h2
    have hΩm : Om (1 + 1) < veblen m (N + 1) := hΩN.trans ((lt_add_one N).trans_le (right_le_veblen _ _))
    obtain ⟨p, q, hp, hmp, hq1, hq2⟩ := udCl_levGe hΩm h hh h1
    have hpa : p ≤ a :=
      udLev_le ((lt_add_one N).trans_le ((right_le_veblen m (N + 1)).trans hq1)) (hq2.trans h2)
    exact LeCl.phi (hA3 Q hQ m p hm hmp hpa hp) (LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ)))

/-- **`φ(a, y' + 1)`, `a > Ω₂` a limit with members `M c` indexed by the codes: the members `φ(M c, N + 1)`.** -/
theorem udMB_levLim {a y' : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hy'H : y' ∈ cdHull S l) (hEG : veblen a (y' + 1) < uaGam) (hB : UaMB S l a) :
    UaMB S l (veblen a (y' + 1)) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen a (y' + 1) with hE_def
  set N := veblen a y' with hN_def
  have ha0 : a ≠ 0 := hlim.ne_bot
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hN1E : N + 1 < E := (taVeb_lim ha0).add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 < N := udG_lt hΩa
  have hΩN : Om (1 + 1) < N := tgOm_lt_G.trans hGN
  have haG : a < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hy1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTlim := uaLimT hl hX a haH hlim haG
  have hTa0 : uaTh S l a ≠ 0 := hTlim.ne_bot
  have hTE : uaTh S l E = veblen (uaTh S l a) (uaTh S l y' + 1) := by
    rw [uaVeb hl hX haH (CSet.succ_mem hy'H) ha0 (hGN.trans hNE).le hEG, uaSucc hl hX hy'H hy1G]
  have hTN : uaTh S l N = veblen (uaTh S l a) (uaTh S l y') := uaVeb hl hX haH hy'H ha0 hGN.le (hNE.trans hEG)
  have hTN1 : uaTh S l N + 1 < uaTh S l E := by
    rw [hTE, hTN]; exact (taVeb_lim hTa0).add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one _))
  have hmE : ∀ m, m < a → veblen m (N + 1) < E := fun m hm => by
    calc veblen m (N + 1) < veblen m E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hm _
  have hown : ∀ Q, SC Q → ∀ m h, LeCl (Om (1 + 1)) Q h → veblen m (N + 1) ≤ h → h ≤ E →
      LeCl (Om (1 + 1)) Q (N + 1) ∧ ∃ p, LeCl (Om (1 + 1)) Q p ∧ m ≤ p ∧ p ≤ a := by
    intro Q hQ m h hh h1 h2
    have hNm : N < veblen m (N + 1) := (lt_add_one N).trans_le (right_le_veblen _ _)
    have hNc := udCl_N hQ hΩN hh (hNm.trans_le h1) h2
    obtain ⟨p, q, hp, hmp, hq1, hq2⟩ := udCl_levGe (hΩN.trans hNm) h hh h1
    exact ⟨LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ)), p, hp, hmp,
      udLev_le (hNm.trans_le hq1) (hq2.trans h2)⟩
  refine ⟨fun c => veblen (M c) (N + 1), fun v => veblen (Mh v) (uaTh S l N + 1),
    fun x z h => veblen_left_monotone _ (hM h), fun x z h => veblen_left_monotone _ (hMh h), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, hM1, hMa, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    refine ⟨CSet.phi_mem hMH (CSet.succ_mem hNH), Order.one_le_iff_pos.2 veblen_pos, hmE _ hMa, ?_, ?_⟩
    · rw [uaVeb hl hX hMH (CSet.succ_mem hNH) (zero_lt_one.trans_le hM1).ne'
        (hGN.le.trans (le_self_add.trans (right_le_veblen _ _))) ((hmE _ hMa).trans hEG),
        uaSucc hl hX hNH (hN1E.trans hEG), hTM]
    · calc veblen (Mh (gxTh (upsilon l) (ldAtR S l) c)) (uaTh S l N + 1)
          < veblen (Mh (gxTh (upsilon l) (ldAtR S l) c)) (uaTh S l E) := (veblen_lt_veblen_iff_right).2 hTN1
        _ = uaTh S l E := by rw [hTE]; exact veblen_veblen_of_lt hMhT _
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := tdCl_levDec hQ ldOm2_SC hlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB1 Q hQ hQ1 c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ hc'M.le)⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := tdCl_levDec hQ tnSC1 hTlim w hw hwE
    rw [← hTN] at hwc'
    obtain ⟨c'', hc''Q, hc'M⟩ := hB2 Q hQ c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ hc'M.le)⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    obtain ⟨hN1c, p, hp, hmp, hpa⟩ := hown Q hQ (M c) h hh h1 h2
    exact LeCl.phi (hB3 Q hQ c p hc1 hcQ hmp hpa hp) hN1c

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ud
