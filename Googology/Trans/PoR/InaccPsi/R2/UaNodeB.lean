import Googology.Trans.PoR.InaccPsi.R2.UaNodeW

/-!
# Member systems of the nodes in the windows: limit levels, limit arguments; every limit exponent below `X₃`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `F_u = φ(Ω₂, u)`
(windows `(F_u, F_{u+1})`, `u ≥ 1`), `X₃ = Ua.uaX3 = φ(Ω₂ + 1, 0)`, `N = φ(a, y')`.

* `uaTh_max` (`T(max x z) = max (T x) (T z)`);
* `uaMA_levLim` (**a limit code level `a` in a window: members `φ(c', N + 1)`, `1 ≤ c' < a` of `H_λ`**),
  `uaMA_argLim`, `uaMB_argLim` (**a limit argument `y > F_u`: the members of `y` above `F_u` (resp. `max(M c,
  F_u + 1)`) lifted through `φ(a, ·)`**);
* `uaNodeMS` (**every node strictly inside a window, `1 ≤ a < Ω₂` a code, has a member system**, given one for
  its argument when that is a limit), `uaNodeAll` (**every node `G ≤ r < X₃`**: at the level `Ω₂` by
  `Ua.uaNodeW`, otherwise in its window);
* `uaMS3` (**EVERY LIMIT EXPONENT `e + r < X₃` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM**: off the nodes
  along the base-`Ω₂` normal form, at the nodes `< G` by `Tx.txMS`, at the nodes `≥ G` by `uaNodeAll`).

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

/-- `T(max x z) = max (T x) (T z)`. -/
theorem uaTh_max {x z : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hzH : z ∈ cdHull S l) (hxE : x < uaGam)
    (hzE : z < uaGam) : uaTh S l (max x z) = max (uaTh S l x) (uaTh S l z) := by
  rcases le_total x z with h | h
  · rw [max_eq_right h, max_eq_right (uaLe hl hX hxH hzH hzE h)]
  · rw [max_eq_left h, max_eq_left (uaLe hl hX hzH hxH hxE h)]

/-- **A limit code level `a` in a window: countable members `φ(c', N + 1)`, `1 ≤ c' < a`** (`F_u ≤ N = φ(a, y')`,
`φ(a, y' + 1) < F_{u+1}`, `u ≥ 1`). -/
theorem uaMA_levLim {u a y' : Ordinal.{0}} (hu1 : 1 ≤ u) (haH : a ∈ cdHull S l) (hlim : IsSuccLimit a)
    (haW : a < Om (1 + 1)) (hy'H : y' ∈ cdHull S l) (hFN : veblen (Om (1 + 1)) u ≤ veblen a y')
    (hEX : veblen a (y' + 1) < veblen (Om (1 + 1)) (u + 1)) (hEG : veblen a (y' + 1) < uaGam) :
    UaMA S l (veblen a (y' + 1)) := by
  have hGN : veblen (Om (1 + 1)) 1 ≤ veblen a y' := (uaG_le_F hu1).trans hFN
  set E := veblen a (y' + 1) with hE_def
  set N := veblen a y' with hN_def
  set M := N + 1 with hM_def
  have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 haH
  have h1a : 1 ≤ a := (rvLim_one_lt hlim).le
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hNH : N ∈ cdHull S l := CSet.phi_mem haH hy'H
  have hMH : M ∈ cdHull S l := CSet.succ_mem hNH
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim ha0
  have hME : M < E := hElim.add_one_lt hNE
  have hGE : veblen (Om (1 + 1)) 1 ≤ E := hGN.trans hNE.le
  have hmE : ∀ c', c' < a → veblen c' M < E := fun c' hc' => by
    calc veblen c' M < veblen c' E := (veblen_lt_veblen_iff_right).2 hME
      _ = E := veblen_veblen_of_lt hc' _
  have hGM : veblen (Om (1 + 1)) 1 < M := hGN.trans_lt (lt_add_one N)
  have hFM : veblen (Om (1 + 1)) u < M := hFN.trans_lt (lt_add_one N)
  have hy'1G : y' + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTN : uaTh S l N = veblen (gxTh (upsilon l) (ldAtR S l) a) (uaTh S l y') := by
    rw [uaVeb hl hX haH hy'H ha0 hGN (hNE.trans hEG), uaThCode hl hX haW]
  have hTE : uaTh S l E = veblen (gxTh (upsilon l) (ldAtR S l) a) (uaTh S l y' + 1) := by
    rw [uaVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEG, uaThCode hl hX haW, uaSucc hl hX hy'H hy'1G]
  have hTm : ∀ c', c' ∈ cdHull S l → 1 ≤ c' → c' < a →
      uaTh S l (veblen c' M) = veblen (gxTh (upsilon l) (ldAtR S l) c') (uaTh S l N + 1) := by
    intro c' hc'H hc'1 hc'a
    rw [uaVeb hl hX hc'H hMH (zero_lt_one.trans_le hc'1).ne' (hGM.le.trans (right_le_veblen _ _))
      ((hmE c' hc'a).trans hEG), uaThCode hl hX (hc'a.trans haW), uaSucc hl hX hNH (hME.trans hEG)]
  refine ⟨fun m => ∃ c', c' ∈ cdHull S l ∧ 1 ≤ c' ∧ c' < a ∧ m = veblen c' M, ?_,
    ⟨_, 1, CSet.one_mem _ _, le_rfl, rvLim_one_lt hlim, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨c', hc'H, -, hc'a, rfl⟩
    exact ⟨CSet.phi_mem hc'H hMH, Order.one_le_iff_pos.2 veblen_pos, hmE c' hc'a⟩
  · intro y hyH hy
    obtain ⟨c', hc'H, hc'a, hyc⟩ := tdHull_levDec hlim y hyH hy
    refine ⟨_, ⟨c' + 1, CSet.succ_mem hc'H, le_add_self, hlim.add_one_lt hc'a, rfl⟩, ?_⟩
    calc y < veblen c' (N + 1) := hyc
      _ ≤ veblen (c' + 1) (N + 1) := veblen_left_monotone (N + 1) le_self_add
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
    calc w < veblen d (uaTh S l N + 1) := hwd
      _ ≤ veblen (d + 1) (uaTh S l N + 1) := veblen_left_monotone _ le_self_add
  · rintro Q hQ m h ⟨c', -, hc'1, hc'a, rfl⟩ h1 h2 hh
    have hX2 : h < veblen (Om (1 + 1)) (u + 1) := h2.trans_lt hEX
    have hc'c := uaCl_levW hQ (hc'a.trans haW) (hFM.trans_le (right_le_veblen _ _)) h hh h1 hX2
    have hNlt : N < h := (lt_add_one N).trans_le ((right_le_veblen c' M).trans h1)
    have hNc := uaCl_NWin hQ haW hFN hh hNlt h2 hX2
    exact LeCl.phi hc'c (LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ)))

/-- **A limit argument `y > F_u` with countable members** (`φ(a, y) < F_{u+1}`): the members `φ(a, m)`,
`m > F_u`. -/
theorem uaMA_argLim {u a y : Ordinal.{0}} (hu1 : 1 ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l) (hylim : IsSuccLimit y)
    (hGy : veblen (Om (1 + 1)) u < y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEG : veblen a y < uaGam) (hA : UaMA S l y) : UaMA S l (veblen a y) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  set E := veblen a y with hE_def
  set G := veblen (Om (1 + 1 : Ordinal.{0})) u with hG_def
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hyE : y ≤ E := right_le_veblen a y
  have hyG : y < uaGam := hyE.trans_lt hEG
  have hGH : G ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) huH
  have hTGy : uaTh S l G < uaTh S l y := uaLt hl hX hGH hyH hyG hGy
  have hmE : ∀ m, Mem m → veblen a m < E := fun m hm => (veblen_lt_veblen_iff_right).2 (hdat m hm).2.2
  have hGle : ∀ m, G < m → veblen (Om (1 + 1)) 1 ≤ veblen a m := fun m h =>
    (uaG_le_F hu1).trans (h.le.trans (right_le_veblen _ _))
  have hTm : ∀ m, Mem m → G < m → uaTh S l (veblen a m) =
      veblen (gxTh (upsilon l) (ldAtR S l) a) (uaTh S l m) := fun m hm hGm => by
    rw [uaVeb hl hX haH (hdat m hm).1 ha0 (hGle m hGm) ((hmE m hm).trans hEG), uaThCode hl hX haW]
  obtain ⟨m0, hm0, hGm0⟩ := hA1 G hGH hGy
  refine ⟨fun m' => ∃ m, Mem m ∧ G < m ∧ m' = veblen a m, ?_, ⟨_, m0, hm0, hGm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, -, rfl⟩
    exact ⟨CSet.phi_mem haH (hdat m hm).1, Order.one_le_iff_pos.2 veblen_pos, hmE m hm⟩
  · intro y0 hy0H hy0
    by_cases h0 : veblen a 0 ≤ y0
    swap
    · push Not at h0
      exact ⟨_, ⟨m0, hm0, hGm0, rfl⟩, h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le)⟩
    obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hy0H h0
    have huy : u < y := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hy0)
    have hmaxH : max u G ∈ cdHull S l := by
      rcases le_total u G with h | h
      · rw [max_eq_right h]; exact hGH
      · rw [max_eq_left h]; exact huH
    obtain ⟨m, hm, hmm⟩ := hA1 _ hmaxH (max_lt huy hGy)
    refine ⟨_, ⟨m, hm, (le_max_right u G).trans_lt hmm, rfl⟩, hu2.trans_le ((veblen_le_veblen_iff_right).2 ?_)⟩
    exact Order.add_one_le_of_lt ((le_max_left u G).trans_lt hmm)
  · intro w hw
    rw [uaVeb hl hX haH hyH ha0 ((uaG_le_F hu1).trans (hGy.le.trans hyE)) hEG, uaThCode hl hX haW] at hw
    have hTlim : IsSuccLimit (uaTh S l y) := uaLimT hl hX y hyH hylim hyG
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hu' hTGy)
    have hGm : G < m := by
      by_contra hc
      push Not at hc
      have := uaLe hl hX (hdat m hm).1 hGH (hGy.trans hyG) hc
      exact absurd ((le_max_right _ _).trans_lt hmm) (not_lt.2 this)
    refine ⟨_, ⟨m, hm, hGm, rfl⟩, ?_⟩
    rw [hTm m hm hGm]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 ((le_max_left _ _).trans_lt hmm))
  · rintro Q hQ m' h ⟨m, hm, hGm, rfl⟩ h1 h2 hh
    have hGam : G < veblen a m := hGm.trans_le (right_le_veblen _ _)
    obtain ⟨hac', v, hv, hmv, hvy⟩ := uaCl_argW hQ haW hGam hh h1 h2 (h2.trans_lt hEX)
    exact LeCl.phi hac' (hA3 Q hQ m v hm hmv hvy hv)

/-- **A limit argument `y > F_u` with members indexed by the codes**: the members `φ(a, max (M c) (F_u + 1))`. -/
theorem uaMB_argLim {u a y : Ordinal.{0}} (hu1 : 1 ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l) (hylim : IsSuccLimit y)
    (hGy : veblen (Om (1 + 1)) u < y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEG : veblen a y < uaGam) (hB : UaMB S l y) : UaMB S l (veblen a y) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen a y with hE_def
  set G := veblen (Om (1 + 1 : Ordinal.{0})) u with hG_def
  set Θa := gxTh (upsilon l) (ldAtR S l) a with hΘa_def
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hΘaO : Θa < Om 1 := snTh_lt_Om1 hl hX haW.le
  have hyE : y ≤ E := right_le_veblen a y
  have hyG : y < uaGam := hyE.trans_lt hEG
  have hGH : G ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) huH
  have hG1H : G + 1 ∈ cdHull S l := CSet.succ_mem hGH
  have hG1y : G + 1 < y := hylim.add_one_lt hGy
  have hG1G : G + 1 < uaGam := hG1y.trans hyG
  set Gh := uaTh S l G with hGh_def
  have hTG1 : uaTh S l (G + 1) = Gh + 1 := uaSucc hl hX hGH hG1G
  have hTlim : IsSuccLimit (uaTh S l y) := uaLimT hl hX y hyH hylim hyG
  have hGh1y : Gh + 1 < uaTh S l y := by
    rw [← hTG1]; exact uaLt hl hX hG1H hyH hyG hG1y
  have hG1le : ∀ m, G + 1 ≤ m → veblen (Om (1 + 1)) 1 ≤ veblen a m := fun m h =>
    (uaG_le_F hu1).trans ((le_self_add.trans h).trans (right_le_veblen _ _))
  have hTE : uaTh S l E = veblen Θa (uaTh S l y) := by
    rw [uaVeb hl hX haH hyH ha0 ((uaG_le_F hu1).trans (hGy.le.trans hyE)) hEG, uaThCode hl hX haW]
  set M' : Ordinal.{0} → Ordinal.{0} := fun c => max (M c) (G + 1) with hM'_def
  set Mh' : Ordinal.{0} → Ordinal.{0} := fun v => max (Mh v) (Gh + 1) with hMh'_def
  have hM'G : ∀ c, G < M' c := fun c => (lt_add_one G).trans_le (le_max_right _ _)
  refine ⟨fun c => veblen a (M' c), fun c => veblen Θa (Mh' c),
    fun x z h => (veblen_le_veblen_iff_right).2 (max_le_max (hM h) le_rfl),
    fun x z h => (veblen_le_veblen_iff_right).2 (max_le_max (hMh h) le_rfl), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, -, hMy, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    have hM'H : M' c ∈ cdHull S l := by
      show max (M c) (G + 1) ∈ cdHull S l
      rcases le_total (M c) (G + 1) with h | h
      · rw [max_eq_right h]; exact hG1H
      · rw [max_eq_left h]; exact hMH
    have hM'y : M' c < y := max_lt hMy hG1y
    have hlt : veblen a (M' c) < E := (veblen_lt_veblen_iff_right).2 hM'y
    refine ⟨CSet.phi_mem haH hM'H, Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [uaVeb hl hX haH hM'H ha0 (hG1le _ (le_max_right _ _)) (hlt.trans hEG), uaThCode hl hX haW]
      show veblen Θa (uaTh S l (max (M c) (G + 1))) =
        veblen Θa (max (Mh (gxTh (upsilon l) (ldAtR S l) c)) (Gh + 1))
      rw [uaTh_max hl hX hMH hG1H (hMy.trans hyG) hG1G, hTM, hTG1]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 (max_lt hMhT hGh1y)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u', hu, huy, hwu⟩ := taCl_dec hQ ldOm2_SC haW hylim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u' hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u', hu, huy, hwu⟩ := taCl_dec hQ Ph.ph_SC_Om1 hΘaO hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u' hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    have hGam : G < veblen a (M' c) := (hM'G c).trans_le (right_le_veblen _ _)
    have hX2 : h < veblen (Om (1 + 1)) (u + 1) := h2.trans_lt hEX
    obtain ⟨hac', v, hv, hmv, hvy⟩ := uaCl_argW hQ haW hGam hh h1 h2 hX2
    refine LeCl.phi hac' ?_
    show LeCl (Om (1 + 1)) Q (max (M c) (G + 1))
    rcases le_total (M c) (G + 1) with hle | hle
    · rw [max_eq_right hle]
      exact LeCl.add (uaCl_FW hQ hh (hGam.le.trans h1) hX2) (LeCl.small (gg_one_lt_of_SC hQ))
    · rw [max_eq_left hle]
      have hmv' : M c ≤ v := (le_max_left (M c) (G + 1)).trans hmv
      exact hB3 Q hQ c v hc1' hcQ hmv' hvy hv

/-- **Every node `φ(a, y)` strictly inside a window `(F_u, F_{u+1})` (`u ≥ 1`, `1 ≤ a < Ω₂` a code) has a member
system**, given one for `y` when `y` is a limit. -/
theorem uaNodeMS {u a y : Ordinal.{0}} (hu1 : 1 ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l)
    (hFE : veblen (Om (1 + 1)) u < veblen a y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEG : veblen a y < uaGam) (IH : IsSuccLimit y → UaMA S l y ∨ UaMB S l y) :
    UaMA S l (veblen a y) ∨ UaMB S l (veblen a y) := by
  have hFy : veblen (Om (1 + 1)) u < y := by
    by_contra hc
    push Not at hc
    have h1 : veblen a y ≤ veblen a (veblen (Om (1 + 1)) u) := (veblen_le_veblen_iff_right).2 hc
    rw [veblen_veblen_of_lt haW] at h1
    exact absurd hFE (not_lt.2 h1)
  rcases zero_or_succ_or_isSuccLimit y with h0 | ⟨y', hy'⟩ | hyl
  · rw [h0] at hFy; exact absurd hFy (not_lt.2 zero_le)
  · rw [succ_eq_add_one] at hy'
    subst hy'
    have hy'H : y' ∈ cdHull S l := mem_of_add_one_mem hyH
    have hFy' : veblen (Om (1 + 1)) u ≤ y' := Order.lt_add_one_iff.1 hFy
    have hFN : veblen (Om (1 + 1)) u ≤ veblen a y' := hFy'.trans (right_le_veblen _ _)
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at h1a; exact absurd h1a (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      have ha'H : a' ∈ cdHull S l := mem_of_add_one_mem haH
      rcases eq_or_ne a' 0 with rfl | ha'0
      · rw [zero_add] at hEX hFN hEG ⊢
        exact Or.inl (uaMA_towW hl hX hu1 hy'H hFN hEX hEG)
      · exact Or.inl (uaMA_towV hl hX hu1 ha'H (Order.one_le_iff_ne_zero.2 ha'0) haW hy'H hFN hEX hEG)
    · exact Or.inl (uaMA_levLim hl hX hu1 haH hal haW hy'H hFN hEX hEG)
  · rcases IH hyl with hA | hB
    · exact Or.inl (uaMA_argLim hl hX hu1 huH haH h1a haW hyH hyl hFy hEX hEG hA)
    · exact Or.inr (uaMB_argLim hl hX hu1 huH haH h1a haW hyH hyl hFy hEX hEG hB)

/-- **The member system of a node `G ≤ r < X₃`**: `r = φ(Ω₂, b)` by `Ua.uaNodeW`, or `r` strictly inside a window
with a code level by `uaNodeMS`. -/
theorem uaNodeAll {r : Ordinal.{0}} (hrH : r ∈ cdHull S l) (hGr : veblen (Om (1 + 1)) 1 ≤ r) (hrX : r < uaX3)
    (hrs : ¬ sgLW r < r) (IH : IsSuccLimit (invVeblen₂ r) → UaMA S l (invVeblen₂ r) ∨ UaMB S l (invVeblen₂ r)) :
    UaMA S l r ∨ UaMB S l r := by
  have hrG : r < uaGam := hrX.trans uaX3_lt_Gam
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := uaNode hGr hrG hrs
  set a := invVeblen₁ r with ha_def
  set y := invVeblen₂ r with hy_def
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  have haW : a ≤ Om (1 + 1) := uaX3_lev (by rw [hv]; exact hrX)
  rcases haW.lt_or_eq with haW | haW
  · -- a code level: the window of `r`
    have hΩr : veblen (Om (1 + 1)) 0 ≤ r := by
      rw [ldOm2_SC.veblen_zero]; exact tgOm_lt_G.le.trans hGr
    obtain ⟨u, huH, hu1', hu2'⟩ := txHull_idx hrH hΩr
    have hne : veblen (Om (1 + 1)) u ≠ r := by
      intro he
      have hfix : veblen a r = r := by rw [← he]; exact veblen_veblen_of_lt haW _
      have : y = r := by
        have h2 : veblen a y = veblen a r := by rw [hv, hfix]
        exact veblen_injective a h2
      exact absurd (this ▸ hbE) (lt_irrefl _)
    have hu1 : 1 ≤ u := by
      by_contra hc
      push Not at hc
      rw [Order.lt_one_iff] at hc
      rw [hc, zero_add] at hu2'
      exact absurd hGr (not_le.2 hu2')
    have h := uaNodeMS hl hX hu1 huH hmem.1 (Order.one_le_iff_pos.2 ha0) haW hmem.2
      (by rw [hv]; exact lt_of_le_of_ne hu1' hne) (by rw [hv]; exact hu2') (by rw [hv]; exact hrG) IH
    rwa [hv] at h
  · -- the level `Ω₂`
    have hy1 : 1 ≤ y := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      rw [haW, h0, ldOm2_SC.veblen_zero] at hv
      rw [← hv] at hGr
      exact absurd hGr (not_le.2 tgOm_lt_G)
    have h := uaNodeW hl hX hmem.2 hy1 (by rw [← haW, hv]; exact hrG) IH
    rwa [← haW, hv] at h

/-- **EVERY LIMIT EXPONENT `e + r < X₃` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM.** -/
theorem uaMS3 : ∀ r, r ∈ cdHull S l → IsSuccLimit r → ∀ e, e ∈ cdHull S l →
    e + r < uaX3 → leWe (sgLW r + 1) ∣ e → UaMA S l (e + r) ∨ UaMB S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hrlim e heH hlt hd
  have hltG : e + r < uaGam := hlt.trans uaX3_lt_Gam
  have hrE : r < uaX3 := le_add_self.trans_lt hlt
  have hr0 : 0 < r := hrlim.bot_lt
  by_cases hrs : sgLW r < r
  swap
  · have hWr : leWe r = r := uaW_fix hr0 hrs
    have hsr : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hrs)
    have hdr : leWe r ∣ e := (leWe_dvd (le_self_add : r ≤ r + 1)).trans (by rw [← hsr]; exact hd)
    have hlt' : e + leWe r < uaGam := by rw [hWr]; exact hltG
    have hMS : UaMA S l r ∨ UaMB S l r := by
      rcases lt_or_ge r (veblen (Om (1 + 1)) 1) with hrG | hrG
      · have h := txMS hl hX r hrH hrlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
        rw [zero_add] at h
        rcases h with hA | hB
        · exact Or.inl (uaMA_of_tu hl hX hrG hA)
        · exact Or.inr (uaMB_of_tu hl hX hrG hB)
      have hbE := (uaNode hrG (hrE.trans uaX3_lt_Gam) hrs).2.2.2.2.1
      have hv := (uaNode hrG (hrE.trans uaX3_lt_Gam) hrs).2.1
      have haE := (uaNode hrG (hrE.trans uaX3_lt_Gam) hrs).2.2.2.1
      have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
      refine uaNodeAll hl hX hrH hrG hrE hrs fun hyl => ?_
      have h := IH _ hbE hmem.2 hyl 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hbE.trans hrE) (dvd_zero _)
      rwa [zero_add] at h
    rw [← hWr]
    rcases hMS with hA | hB
    · exact Or.inl (uaMA_lift hl hX heH hrH hdr hlt' hA)
    · exact Or.inr (uaMB_lift hl hX heH hrH hdr hlt' hB)
  obtain ⟨hfH, -, hcc, hc1, hcW, hr'H, hr'f, hrdec⟩ := uaBase hl hX hrH hr0
  have hfr : sgLW r < r := hrs
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
      have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
      have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
      have he2r : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
      have hd2 : leWe f ∣ e + leWe f * c1 := dvd_add hdf (dvd_mul_right _ _)
      have hlt2 : e + leWe f * c1 + leWe f < uaGam := he2r ▸ hltG
      rw [← he2r]
      rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f1, hfs⟩ | hflim
      · exfalso
        have hrc1 : r = c1 + 1 := by rw [hrc, hf0, leWe_zero, one_mul, ← hcs]
        have h := hrlim.succ_lt (show c1 < r from hrc1 ▸ lt_add_one c1)
        rw [Order.succ_eq_add_one, ← hrc1] at h
        exact lt_irrefl _ h
      · rw [succ_eq_add_one] at hfs
        have hf1H : f1 ∈ cdHull S l := mem_of_add_one_mem (hfs ▸ hfH)
        rw [← hfs] at hd2 hlt2 he2H ⊢
        exact Or.inr (uaMB_succ hl hX he2H hf1H hd2 hlt2)
      · have hMSf := IH f hfr hfH hflim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hfr.trans hrE)
          (dvd_zero _)
        rw [zero_add] at hMSf
        rcases hMSf with hA | hB
        · exact Or.inl (uaMA_lift hl hX he2H hfH hd2 hlt2 hA)
        · exact Or.inr (uaMB_lift hl hX he2H hfH hd2 hlt2 hB)
    · rw [hrc] at hltG ⊢
      exact Or.inl (uaMA_coef hl hX heH hfH hcc hclim hcW hd hltG)
  · have hr'lim : IsSuccLimit r' := by
      rcases zero_or_succ_or_isSuccLimit r' with h0 | ⟨r1, hr1⟩ | hl'
      · exact absurd h0 hr'0
      · exfalso
        rw [succ_eq_add_one] at hr1
        have hr2 : r = leWe f * c + r1 + 1 := by rw [add_assoc, hr1]; exact hrdec
        have h := hrlim.succ_lt (show leWe f * c + r1 < r from hr2 ▸ lt_add_one _)
        rw [Order.succ_eq_add_one, ← hr2] at h
        exact lt_irrefl _ h
      · exact hl'
    have hs' : sgLW r' < f := tuLogW_lt hr'0 hr'f
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have h := IH r' hr'r hr'H hr'lim (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hlt) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
    rwa [he2] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua
