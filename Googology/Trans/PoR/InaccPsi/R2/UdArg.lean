import Googology.Trans.PoR.InaccPsi.R2.UdLim

/-!
# Member systems of the nodes `φ(a, 0)` (`a > Ω₂` a limit) and `φ(a, y)` (`a > Ω₂`, `y` a limit)

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `Γ₂ = Ua.uaGam`, member systems
`Ua.UaMA`, `Ua.UaMB`.

* `udMA_lev0`, `udMB_lev0` (**`φ(a, 0)`, `a > Ω₂` a limit: the members `φ(m, 0)` for the members `m > Ω₂` of `a`**;
  for `UaMB` the members `φ(max (M c) (Ω₂ + 1), 0)`);
* `udMA_argLim`, `udMB_argLim` (**`φ(a, y)`, `a > Ω₂`, `y` a limit: the members `φ(a, m)` for the members `m > t` of
  `y`**, `t` the threshold `Ud.udThr`; for `UaMB` the members `φ(a, max (M c) (t + 1))`).

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

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- The own transfer at a node `φ(m, 0) ≤ h ≤ φ(a, 0)` (`m > Ω₂`): a code level `p` with `m ≤ p ≤ a`. -/
theorem udOwn0 {Q a m h : Ordinal.{0}} (hm : Om (1 + 1) < m) (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen m 0 ≤ h)
    (h2 : h ≤ veblen a 0) : ∃ p, LeCl (Om (1 + 1)) Q p ∧ m ≤ p ∧ p ≤ a := by
  obtain ⟨p, q, hp, hmp, -, hq2⟩ := udCl_levGe (hm.trans_le (left_le_veblen m 0)) h hh h1
  exact ⟨p, hp, hmp, udLev_le0 (hq2.trans h2)⟩

/-- **`φ(a, 0)`, `a > Ω₂` a limit with countable members: the members `φ(m, 0)`, `m > Ω₂`.** -/
theorem udMA_lev0 {a : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hEG : veblen a 0 < uaGam) (hA : UaMA S l a) : UaMA S l (veblen a 0) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  have ha0 : a ≠ 0 := hlim.ne_bot
  have haG : a < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hΩH : Om (1 + 1) ∈ cdHull S l := mxOm2_mem _ _
  have hTE : uaTh S l (veblen a 0) = veblen (uaTh S l a) 0 := by
    rw [uaVeb hl hX haH (CSet.zero_mem _ _) ha0 (udG_lt hΩa).le hEG, uaTh_zero]
  have hmE : ∀ m, m < a → veblen m 0 < veblen a 0 := fun m hm => veblen_zero_strictMono hm
  have hTm : ∀ m, Mem m → Om (1 + 1) < m → uaTh S l (veblen m 0) = veblen (uaTh S l m) 0 := fun m hm hΩm => by
    obtain ⟨hmH, hm1, hma⟩ := hdat m hm
    rw [uaVeb hl hX hmH (CSet.zero_mem _ _) (zero_lt_one.trans_le hm1).ne' (udG_lt hΩm).le
      ((hmE m hma).trans hEG), uaTh_zero]
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
    have hTlim := uaLimT hl hX a haH hlim haG
    obtain ⟨d, hd, hwd⟩ := udLev0 hTlim hw
    have hTΩ : uaTh S l (Om (1 + 1)) < uaTh S l a := uaLt hl hX hΩH haH haG hΩa
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hd hTΩ)
    have hΩm : Om (1 + 1) < m := by
      by_contra hc
      push Not at hc
      exact absurd ((le_max_right _ _).trans_lt hmm) (not_lt.2 (uaLe hl hX (hdat m hm).1 hΩH
        (tgOm_lt_G.trans uaG_lt_Gam) hc))
    refine ⟨_, ⟨m, hm, hΩm, rfl⟩, ?_⟩
    rw [hTm m hm hΩm]
    exact hwd.trans_le (veblen_left_monotone _ ((le_max_left _ _).trans hmm.le))
  · rintro Q hQ m' h ⟨m, hm, hΩm, rfl⟩ h1 h2 hh
    obtain ⟨p, hp, hmp, hpa⟩ := udOwn0 hΩm hh h1 h2
    exact LeCl.phi (hA3 Q hQ m p hm hmp hpa hp) (LeCl.zero hQ.1)

/-- **`φ(a, 0)`, `a > Ω₂` a limit with members `M c` indexed by the codes: the members `φ(max (M c) (Ω₂+1), 0)`.** -/
theorem udMB_lev0 {a : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hlim : IsSuccLimit a)
    (hEG : veblen a 0 < uaGam) (hB : UaMB S l a) : UaMB S l (veblen a 0) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have ha0 : a ≠ 0 := hlim.ne_bot
  have haG : a < uaGam := (left_le_veblen _ _).trans_lt hEG
  have hΩH : Om (1 + 1) ∈ cdHull S l := mxOm2_mem _ _
  have hΩ1H : Om (1 + 1) + 1 ∈ cdHull S l := CSet.succ_mem hΩH
  have hΩ1a : Om (1 + 1) + 1 < a := hlim.add_one_lt hΩa
  have hΩ1G : Om (1 + 1) + 1 < uaGam := hΩ1a.trans haG
  have hTlim := uaLimT hl hX a haH hlim haG
  set K := uaTh S l (Om (1 + 1)) with hK
  have hTΩ1 : uaTh S l (Om (1 + 1) + 1) = K + 1 := uaSucc hl hX hΩH hΩ1G
  have hK1a : K + 1 < uaTh S l a := by rw [← hTΩ1]; exact uaLt hl hX hΩ1H haH haG hΩ1a
  have hTE : uaTh S l (veblen a 0) = veblen (uaTh S l a) 0 := by
    rw [uaVeb hl hX haH (CSet.zero_mem _ _) ha0 (udG_lt hΩa).le hEG, uaTh_zero]
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
    · rw [uaVeb hl hX hmxH (CSet.zero_mem _ _) (zero_lt_one.trans_le (le_add_self.trans (le_max_right _ _))).ne'
        (udG_lt hΩmx).le (hlt.trans hEG), uaTh_zero, uaTh_max hl hX hMH hΩ1H (hMa.trans haG) hΩ1G, hTM, hTΩ1]
    · rw [hTE]; exact veblen_zero_strictMono (max_lt hMhT hK1a)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := udCl_levDec0 hQ ldOm2_SC hlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB1 Q hQ hQ1 c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ (hc'M.le.trans (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'a, hwc'⟩ := udCl_levDec0 hQ tnSC1 hTlim w hw hwE
    obtain ⟨c'', hc''Q, hc'M⟩ := hB2 Q hQ c' hc' hc'a
    exact ⟨c'', hc''Q, hwc'.trans_le (veblen_left_monotone _ (hc'M.le.trans (le_max_left _ _)))⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have hΩmx : Om (1 + 1) < max (M c) (Om (1 + 1) + 1) := (lt_add_one _).trans_le (le_max_right _ _)
    obtain ⟨p, hp, hmp, hpa⟩ := udOwn0 hΩmx hh h1 h2
    refine LeCl.phi ?_ (LeCl.zero hQ.1)
    rcases le_total (M c) (Om (1 + 1) + 1) with hle | hle
    · rw [max_eq_right hle]; exact LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))
    · rw [max_eq_left hle] at hmp ⊢
      exact hB3 Q hQ c p hc1 hcQ hmp hpa hp

omit hl hX in
/-- The own transfer at a node `φ(a, m) ≤ h ≤ φ(a, y)` (`a > Ω₂`, no fixed point of `φ(a, ·)` in `[m, y]`): the
code `a` and a code `u` with `m ≤ u ≤ y`. -/
theorem udOwnArg {Q a m y h : Ordinal.{0}} (hQ : SC Q) (hΩa : Om (1 + 1) < a)
    (hnf : ∀ v, m ≤ v → v ≤ y → veblen a v ≠ v) (hh : LeCl (Om (1 + 1)) Q h) (h1 : veblen a m ≤ h)
    (h2 : h ≤ veblen a y) : LeCl (Om (1 + 1)) Q a ∧ ∃ u, LeCl (Om (1 + 1)) Q u ∧ m ≤ u ∧ u ≤ y := by
  have hΩ : Om (1 + 1) < veblen a m := hΩa.trans_le (left_le_veblen a m)
  have hac := uaCl_levG hQ hΩ h hh h1 fun v hv1 hv2 hfix => by
    have hmv : m ≤ v := by
      have := hv1; rw [← hfix] at this; exact (veblen_le_veblen_iff_right).1 this
    have hvy : v ≤ y := by
      have := hv2.trans h2; rw [← hfix] at this; exact (veblen_le_veblen_iff_right).1 this
    exact hnf v hmv hvy hfix
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx ldOm2_SC hQ.1 h hh h0
  have hlo : m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u ≤ y := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact ⟨hac, u, hu, hlo, hhi⟩

/-- **`φ(a, y)`, `a > Ω₂`, `y` a limit with countable members: the members `φ(a, m)`, `m > t`.** -/
theorem udMA_argLim {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hyH : y ∈ cdHull S l)
    (hylim : IsSuccLimit y) (hyE : y < veblen a y) (hEG : veblen a y < uaGam) (hA : UaMA S l y) :
    UaMA S l (veblen a y) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  obtain ⟨t, htH, hty, hnf, -⟩ := udThr haH hyH hΩa hyE hylim
  have ha0 : a ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hΩa).ne'
  have hyG : y < uaGam := hyE.trans hEG
  have hTE : uaTh S l (veblen a y) = veblen (uaTh S l a) (uaTh S l y) :=
    uaVeb hl hX haH hyH ha0 (udG_lt hΩa).le hEG
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
    have hTlim : IsSuccLimit (uaTh S l y) := uaLimT hl hX y hyH hylim hyG
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    have hTty : uaTh S l t < uaTh S l y := uaLt hl hX htH hyH hyG hty
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hu' hTty)
    have htm : t < m := by
      by_contra hc
      push Not at hc
      exact absurd ((le_max_right _ _).trans_lt hmm)
        (not_lt.2 (uaLe hl hX (hdat m hm).1 htH (hty.trans hyG) hc))
    refine ⟨_, ⟨m, hm, htm, rfl⟩, ?_⟩
    rw [uaVeb hl hX haH (hdat m hm).1 ha0 (udG_lt hΩa).le ((hmE m (hdat m hm).2.2).trans hEG)]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 ((le_max_left _ _).trans_lt hmm))
  · rintro Q hQ m' h ⟨m, hm, htm, rfl⟩ h1 h2 hh
    obtain ⟨hac, u, hu, hmu, huy⟩ :=
      udOwnArg hQ hΩa (fun v hmv hvy => hnf v (htm.trans_le hmv) hvy) hh h1 h2
    exact LeCl.phi hac (hA3 Q hQ m u hm hmu huy hu)

/-- **`φ(a, y)`, `a > Ω₂`, `y` a limit with members `M c` indexed by the codes: the members
`φ(a, max (M c) (t + 1))`.** -/
theorem udMB_argLim {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hΩa : Om (1 + 1) < a) (hyH : y ∈ cdHull S l)
    (hylim : IsSuccLimit y) (hyE : y < veblen a y) (hEG : veblen a y < uaGam) (hB : UaMB S l y) :
    UaMB S l (veblen a y) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  obtain ⟨t, htH, hty, hnf, htc⟩ := udThr haH hyH hΩa hyE hylim
  have ha0 : a ≠ 0 := ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hΩa).ne'
  have hyG : y < uaGam := hyE.trans hEG
  have ht1H : t + 1 ∈ cdHull S l := CSet.succ_mem htH
  have ht1y : t + 1 < y := hylim.add_one_lt hty
  have ht1G : t + 1 < uaGam := ht1y.trans hyG
  have hTlim : IsSuccLimit (uaTh S l y) := uaLimT hl hX y hyH hylim hyG
  set Tt := uaTh S l t with hTt
  have hTt1 : uaTh S l (t + 1) = Tt + 1 := uaSucc hl hX htH ht1G
  have hTt1y : Tt + 1 < uaTh S l y := by rw [← hTt1]; exact uaLt hl hX ht1H hyH hyG ht1y
  have hTE : uaTh S l (veblen a y) = veblen (uaTh S l a) (uaTh S l y) :=
    uaVeb hl hX haH hyH ha0 (udG_lt hΩa).le hEG
  have hΘaO : uaTh S l a ≠ 0 := (uaPos hl hX haH (pos_iff_ne_zero.2 ha0) ((left_le_veblen a y).trans_lt hEG)).ne'
  refine ⟨fun c => veblen a (max (M c) (t + 1)), fun v => veblen (uaTh S l a) (max (Mh v) (Tt + 1)),
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
    · rw [uaVeb hl hX haH hmxH ha0 (udG_lt hΩa).le (hlt.trans hEG),
        uaTh_max hl hX hMH ht1H (hMy.trans hyG) ht1G, hTM, hTt1]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 (max_lt hMhT hTt1y)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u, hu, huy, hwu⟩ := udCl_dec hQ ldOm2_SC hylim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u, hu, huy, hwu⟩ := udCl_dec hQ tnSC1 hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have htm : t < max (M c) (t + 1) := (lt_add_one t).trans_le (le_max_right _ _)
    obtain ⟨hac, u, hu, hmu, huy⟩ :=
      udOwnArg hQ hΩa (fun v hmv hvy => hnf v (htm.trans_le hmv) hvy) hh h1 h2
    refine LeCl.phi hac ?_
    rcases le_total (M c) (t + 1) with hle | hle
    · change veblen a (max (M c) (t + 1)) ≤ h at h1
      rw [max_eq_right hle] at h1 ⊢
      exact htc Q hQ h hh h1 h2
    · rw [max_eq_left hle] at hmu ⊢
      exact hB3 Q hQ c u hc1 hcQ hmu huy hu

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ud
