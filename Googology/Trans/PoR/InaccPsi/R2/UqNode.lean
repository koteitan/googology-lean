import Googology.Trans.PoR.InaccPsi.R2.UqTow

/-!
# Member systems of the window nodes past `Γ₂`, and the level statement up to `φ(Ω₂, Γ₂ + 1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q`,
`CL₃ = Ug.UgCL`, `F_u = φ(Ω₂, u)` (`Γ₂ ≤ u`), `Γ₂ = Ua.uaGam = F_{Γ₂}`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

`Ua.uaMA_levLim`, `Ua.uaMA_argLim`, `Ua.uaMB_argLim`, `Ua.uaNodeMS` past `Γ₂` (φ law `Ug.ugVeb`, level codes, the
fine decomposition `Uq.uqCl_dec` at the levels `1` and `2`, the transfers `Uq.uqCl_levW`, `Uq.uqCl_NWin`,
`Uq.uqCl_argW`, `Uq.uqCl_FW`, the limit lemma `Uq.uqLimT`).

* `uqMA_levLim` (a limit code level), `uqMA_argLim`, `uqMB_argLim` (a limit argument);
* `uqNodeMS` (**EVERY NODE `φ(a, y)` STRICTLY INSIDE A WINDOW `(F_u, F_{u+1})`, `Γ₂ ≤ u`, `1 ≤ a < Ω₂` A CODE, HAS A
  MEMBER SYSTEM**, given one for `y` when `y` is a limit);
* `uqFix_F` (a `W`-fixed `r ∈ (Γ₂, F_{Γ₂+1})` is a node with a code level), `uqFixWin` (**`UqFixMS S λ F_{Γ₂+1}`
  holds**: `Γ₂` by the members `X_k`, the other `W`-fixed limits by `uqNodeMS` in the window `(Γ₂, F_{Γ₂+1})`);
* `uqLevWin` (**UNCONDITIONAL: `UjLev (CL₃ E) E (T E)` AT EVERY LEVEL `Ω₂ ≤ E < φ(Ω₂, Γ₂ + 1)` OF `H_λ`**).

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
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A limit code level `a` in a window past `Γ₂`: countable members `φ(c', N + 1)`, `1 ≤ c' < a`.** -/
theorem uqMA_levLim {u a y' : Ordinal.{0}} (hGu : uaGam ≤ u) (haH : a ∈ cdHull S l) (hlim : IsSuccLimit a)
    (haW : a < Om (1 + 1)) (hy'H : y' ∈ cdHull S l) (hFN : veblen (Om (1 + 1)) u ≤ veblen a y')
    (hEX : veblen a (y' + 1) < veblen (Om (1 + 1)) (u + 1)) (hEY : veblen a (y' + 1) < ugY S) :
    UqMA S l (veblen a (y' + 1)) := by
  have hGN : uaGam ≤ veblen a y' := (uqGam_le_F hGu).trans hFN
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
  have hGE : uaGam ≤ E := hGN.trans hNE.le
  have hmE : ∀ c', c' < a → veblen c' M < E := fun c' hc' => by
    calc veblen c' M < veblen c' E := (veblen_lt_veblen_iff_right).2 hME
      _ = E := veblen_veblen_of_lt hc' _
  have hGM : uaGam ≤ M := hGN.trans (lt_add_one N).le
  have hFM : veblen (Om (1 + 1)) u < M := hFN.trans_lt (lt_add_one N)
  have hy'1Y : y' + 1 < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hTN : ugTh S l N = veblen (gxTh (upsilon l) (ldAtR S l) a) (ugTh S l y') := by
    rw [ugVeb hl hX haH hy'H ha0 hGN (hNE.trans hEY), uqThCode hl hX haW]
  have hTE : ugTh S l E = veblen (gxTh (upsilon l) (ldAtR S l) a) (ugTh S l y' + 1) := by
    rw [ugVeb hl hX haH (CSet.succ_mem hy'H) ha0 hGE hEY, uqThCode hl hX haW, ugSucc hl hX hy'H hy'1Y]
  have hTm : ∀ c', c' ∈ cdHull S l → 1 ≤ c' → c' < a →
      ugTh S l (veblen c' M) = veblen (gxTh (upsilon l) (ldAtR S l) c') (ugTh S l N + 1) := by
    intro c' hc'H hc'1 hc'a
    rw [ugVeb hl hX hc'H hMH (zero_lt_one.trans_le hc'1).ne' (hGM.trans (right_le_veblen _ _))
      ((hmE c' hc'a).trans hEY), uqThCode hl hX (hc'a.trans haW), ugSucc hl hX hNH (hME.trans hEY)]
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
    calc w < veblen d (ugTh S l N + 1) := hwd
      _ ≤ veblen (d + 1) (ugTh S l N + 1) := veblen_left_monotone _ le_self_add
  · rintro Q hQ m h ⟨c', -, hc'1, hc'a, rfl⟩ h1 h2 hh
    have hX2 : h < veblen (Om (1 + 1)) (u + 1) := h2.trans_lt hEX
    have hc'c := uqCl_levW hQ (hc'a.trans haW) (hFM.trans_le (right_le_veblen _ _)) h hh h1 hX2
    have hNlt : N < h := (lt_add_one N).trans_le ((right_le_veblen c' M).trans h1)
    have hNc := uqCl_NWin hQ haW hFN hh hNlt h2 hX2
    exact UgC.phi hc'c (UgC.add hNc (UgC.small (gg_one_lt_of_SC hQ)))

/-- **A limit argument `y > F_u` with countable members** (`φ(a, y) < F_{u+1}`, past `Γ₂`). -/
theorem uqMA_argLim {u a y : Ordinal.{0}} (hGu : uaGam ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l) (hylim : IsSuccLimit y)
    (hGy : veblen (Om (1 + 1)) u < y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEY : veblen a y < ugY S) (hA : UqMA S l y) : UqMA S l (veblen a y) := by
  obtain ⟨Mem, hdat, -, hA1, hA2, hA3⟩ := hA
  set E := veblen a y with hE_def
  set G := veblen (Om (1 + 1 : Ordinal.{0})) u with hG_def
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hyE : y ≤ E := right_le_veblen a y
  have hyY : y < ugY S := hyE.trans_lt hEY
  have hGH : G ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) huH
  have hTGy : ugTh S l G < ugTh S l y := ugLt hl hX hGH hyH hyY hGy
  have hmE : ∀ m, Mem m → veblen a m < E := fun m hm => (veblen_lt_veblen_iff_right).2 (hdat m hm).2.2
  have hGle : ∀ m, G < m → uaGam ≤ veblen a m := fun m h =>
    (uqGam_le_F hGu).trans (h.le.trans (right_le_veblen _ _))
  have hTm : ∀ m, Mem m → G < m → ugTh S l (veblen a m) =
      veblen (gxTh (upsilon l) (ldAtR S l) a) (ugTh S l m) := fun m hm hGm => by
    rw [ugVeb hl hX haH (hdat m hm).1 ha0 (hGle m hGm) ((hmE m hm).trans hEY), uqThCode hl hX haW]
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
    rw [ugVeb hl hX haH hyH ha0 ((uqGam_le_F hGu).trans (hGy.le.trans hyE)) hEY, uqThCode hl hX haW] at hw
    have hTlim : IsSuccLimit (ugTh S l y) := uqLimT hl hX y hyH hylim hyY
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    obtain ⟨m, hm, hmm⟩ := hA2 _ (max_lt hu' hTGy)
    have hGm : G < m := by
      by_contra hc
      push Not at hc
      have := ugLe hl hX (hdat m hm).1 hGH (hGy.trans hyY) hc
      exact absurd ((le_max_right _ _).trans_lt hmm) (not_lt.2 this)
    refine ⟨_, ⟨m, hm, hGm, rfl⟩, ?_⟩
    rw [hTm m hm hGm]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 ((le_max_left _ _).trans_lt hmm))
  · rintro Q hQ m' h ⟨m, hm, hGm, rfl⟩ h1 h2 hh
    have hGam : G < veblen a m := hGm.trans_le (right_le_veblen _ _)
    obtain ⟨hac', v, hv, hmv, hvy⟩ := uqCl_argW hQ haW hGam hh h1 h2 (h2.trans_lt hEX)
    exact UgC.phi hac' (hA3 Q hQ m v hm hmv hvy hv)

/-- **A limit argument `y > F_u` with members indexed by the codes** (past `Γ₂`): the members
`φ(a, max (M c) (F_u + 1))`. -/
theorem uqMB_argLim {u a y : Ordinal.{0}} (hGu : uaGam ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l) (hylim : IsSuccLimit y)
    (hGy : veblen (Om (1 + 1)) u < y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEY : veblen a y < ugY S) (hB : UqMB S l y) : UqMB S l (veblen a y) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen a y with hE_def
  set G := veblen (Om (1 + 1 : Ordinal.{0})) u with hG_def
  set Θa := gxTh (upsilon l) (ldAtR S l) a with hΘa_def
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  have hΘaO : Θa < Om 1 := snTh_lt_Om1 hl hX haW.le
  have hyE : y ≤ E := right_le_veblen a y
  have hyY : y < ugY S := hyE.trans_lt hEY
  have hGH : G ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) huH
  have hG1H : G + 1 ∈ cdHull S l := CSet.succ_mem hGH
  have hG1y : G + 1 < y := hylim.add_one_lt hGy
  have hG1Y : G + 1 < ugY S := hG1y.trans hyY
  set Gh := ugTh S l G with hGh_def
  have hTG1 : ugTh S l (G + 1) = Gh + 1 := ugSucc hl hX hGH hG1Y
  have hTlim : IsSuccLimit (ugTh S l y) := uqLimT hl hX y hyH hylim hyY
  have hGh1y : Gh + 1 < ugTh S l y := by
    rw [← hTG1]; exact ugLt hl hX hG1H hyH hyY hG1y
  have hG1le : ∀ m, G + 1 ≤ m → uaGam ≤ veblen a m := fun m h =>
    (uqGam_le_F hGu).trans ((le_self_add.trans h).trans (right_le_veblen _ _))
  have hTE : ugTh S l E = veblen Θa (ugTh S l y) := by
    rw [ugVeb hl hX haH hyH ha0 ((uqGam_le_F hGu).trans (hGy.le.trans hyE)) hEY, uqThCode hl hX haW]
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
    · rw [ugVeb hl hX haH hM'H ha0 (hG1le _ (le_max_right _ _)) (hlt.trans hEY), uqThCode hl hX haW]
      show veblen Θa (ugTh S l (max (M c) (G + 1))) =
        veblen Θa (max (Mh (gxTh (upsilon l) (ldAtR S l) c)) (Gh + 1))
      rw [uqTh_max hl hX hMH hG1H (hMy.trans hyY) hG1Y, hTM, hTG1]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 (max_lt hMhT hGh1y)
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u', hu, huy, hwu⟩ := uqCl_dec hQ ugTwo_ne haW hylim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u' hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u', hu, huy, hwu⟩ := uqCl_dec hQ one_ne_zero hΘaO hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u' hu huy
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 (huc'.trans_le (le_max_left _ _)))⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    have hGam : G < veblen a (M' c) := (hM'G c).trans_le (right_le_veblen _ _)
    have hX2 : h < veblen (Om (1 + 1)) (u + 1) := h2.trans_lt hEX
    obtain ⟨hac', v, hv, hmv, hvy⟩ := uqCl_argW hQ haW hGam hh h1 h2 hX2
    refine UgC.phi hac' ?_
    show UgC S (1 + 1) Q (max (M c) (G + 1))
    rcases le_total (M c) (G + 1) with hle | hle
    · rw [max_eq_right hle]
      exact UgC.add (uqCl_FW hQ hh (hGam.le.trans h1) hX2) (UgC.small (gg_one_lt_of_SC hQ))
    · rw [max_eq_left hle]
      have hmv' : M c ≤ v := (le_max_left (M c) (G + 1)).trans hmv
      exact hB3 Q hQ c v hc1' hcQ hmv' hvy hv

/-- **EVERY NODE `φ(a, y)` STRICTLY INSIDE A WINDOW `(F_u, F_{u+1})` PAST `Γ₂` (`Γ₂ ≤ u`, `1 ≤ a < Ω₂` a code) HAS A
MEMBER SYSTEM**, given one for `y` when `y` is a limit. -/
theorem uqNodeMS {u a y : Ordinal.{0}} (hGu : uaGam ≤ u) (huH : u ∈ cdHull S l) (haH : a ∈ cdHull S l)
    (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hyH : y ∈ cdHull S l)
    (hFE : veblen (Om (1 + 1)) u < veblen a y) (hEX : veblen a y < veblen (Om (1 + 1)) (u + 1))
    (hEY : veblen a y < ugY S) (IH : IsSuccLimit y → UqMA S l y ∨ UqMB S l y) :
    UqMA S l (veblen a y) ∨ UqMB S l (veblen a y) := by
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
      · rw [zero_add] at hEX hFN hEY ⊢
        exact Or.inl (uqMA_towW hl hX hGu hy'H hFN hEX hEY)
      · exact Or.inl (uqMA_towV hl hX hGu ha'H (Order.one_le_iff_ne_zero.2 ha'0) haW hy'H hFN hEX hEY)
    · exact Or.inl (uqMA_levLim hl hX hGu haH hal haW hy'H hFN hEX hEY)
  · rcases IH hyl with hA | hB
    · exact Or.inl (uqMA_argLim hl hX hGu huH haH h1a haW hyH hyl hFy hEX hEY hA)
    · exact Or.inr (uqMB_argLim hl hX hGu huH haH h1a haW hyH hyl hFy hEX hEY hB)

omit hl hX in
/-- **A `W`-fixed `r ∈ (Γ₂, F_{Γ₂+1})` is a node `φ(a, y)` with a code level `1 ≤ a < Ω₂`, `a, y < r`.** -/
theorem uqFix_F {r : Ordinal.{0}} (hGr : uaGam < r) (hrB : r < veblen (Om (1 + 1)) (uaGam + 1))
    (hrs : ¬ sgLW r < r) :
    veblen (invVeblen₁ r) (invVeblen₂ r) = r ∧ 0 < invVeblen₁ r ∧ invVeblen₁ r < Om (1 + 1) ∧
      invVeblen₁ r < r ∧ invVeblen₂ r < r := by
  have hFG : veblen (Om (1 + 1)) uaGam = uaGam := uaGam_spec.1.veblen_right uaGam_spec.2
  -- `r = F_z` is impossible
  have hnoF : ∀ z, veblen (Om (1 + 1)) z = r → False := by
    intro z hz
    have h1 : uaGam < z := by
      rw [← hz, ← hFG] at hGr; exact (veblen_lt_veblen_iff_right).1 hGr
    have h2 : z < uaGam + 1 := by rw [← hz] at hrB; exact (veblen_lt_veblen_iff_right).1 hrB
    exact absurd (Order.lt_add_one_iff.1 h2) (not_le.2 h1)
  have hS : ¬ SC r := fun hS => hnoF r (hS.veblen_right (uaGam_spec.2.trans hGr))
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := ugNode hGr.le hS hrs
  refine ⟨hv, ha0, ?_, haE, hbE⟩
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · exact hnoF r (by rw [← hv]; exact veblen_veblen_of_lt hlt _)
  · exact hnoF (invVeblen₂ r) (by rw [heq]; exact hv)

omit hl hX in
/-- `F_{Γ₂+1} = φ(Ω₂, Γ₂ + 1) < Y₃`. -/
theorem uqFW_lt_Y : veblen (Om (1 + 1)) (uaGam + 1) < ugY S :=
  uqY_SC.2 _ uqW_lt_Y _ (uqY_SC.isSuccLimit.add_one_lt ujGam_lt_Y)

/-- **`UqFixMS S λ F_{Γ₂+1}`**: `Γ₂` by the members `X_k`, every other `W`-fixed limit in `(Γ₂, F_{Γ₂+1})` by
`uqNodeMS` in the window `(F_{Γ₂}, F_{Γ₂+1}) = (Γ₂, F_{Γ₂+1})`. -/
theorem uqFixWin : UqFixMS S l (veblen (Om (1 + 1)) (uaGam + 1)) := by
  intro r hrH hGr hrB hrs IH
  rcases hGr.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact Or.inl (uqMA_gam hl hX)
  obtain ⟨hv, ha0, haW, haE, hbE⟩ := uqFix_F hlt hrB hrs
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  have hFG : veblen (Om (1 + 1)) uaGam = uaGam := uaGam_spec.1.veblen_right uaGam_spec.2
  have h := uqNodeMS hl hX le_rfl (ugGam_mem l) hmem.1 (Order.one_le_iff_pos.2 ha0) haW hmem.2
    (by rw [hFG, hv]; exact hlt) (by rw [hv]; exact hrB) (by rw [hv]; exact hrB.trans uqFW_lt_Y)
    (fun hyl => IH _ hmem.2 hyl hbE)
  rwa [hv] at h

/-- **UNCONDITIONAL: THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < φ(Ω₂, Γ₂ + 1)` OF `H_λ`** (image `T E`,
own predicate `CL₃ E`). -/
theorem uqLevWin {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < veblen (Om (1 + 1)) (uaGam + 1)) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevB hl hX (uqFixWin hl hX) uqFW_lt_Y.le (taVeb_lim ldOm2_SC.1.ne') hEH hWE hE

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
