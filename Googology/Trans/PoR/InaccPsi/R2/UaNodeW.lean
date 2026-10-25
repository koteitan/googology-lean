import Googology.Trans.PoR.InaccPsi.R2.UaNode

/-!
# Member systems of the nodes at the level `Ω₂`: `φ(Ω₂, b)`, `b ≥ 1`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, `F_b = φ(Ω₂, b)`,
`T F_b = φ(Ω₁, T b)`.

* `uaThF` (`T(φ(Ω₂, b)) = φ(Ω₁, T b)` for `b ≥ 1`);
* `uaMB_W` (**`φ(Ω₂, b + 1)`, `b ≥ 1`: members `φ(c, F_b + 1)` indexed by the codes `c`**, images
  `φ(Θ c, T F_b + 1)`; the own transfer by `Ua.uaCl_NW`, the index lemma at the level `Ω₂`; `Ua.uaMB_G` is `b = 0`);
* `uaMA_Wlim`, `uaMB_Wlim` (**`φ(Ω₂, b)`, `b` a limit: the members of `b` lifted through `φ(Ω₂, ·)`**; the own
  transfer by `Ua.uaCl_idx` at the level `Ω₂` — the level `Ω₂` is always a code);
* `uaNodeW` (**every node `φ(Ω₂, b)`, `1 ≤ b < φ(Ω₂, b) < Γ₂`, has a member system**, given one for `b` when `b`
  is a limit).

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

/-- `T(φ(Ω₂, b)) = φ(Ω₁, T b)` for `b ≥ 1` (`φ(Ω₂, b) < Γ₂`). -/
theorem uaThF {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b) (hEG : veblen (Om (1 + 1)) b < uaGam) :
    uaTh S l (veblen (Om (1 + 1)) b) = veblen (Om 1) (uaTh S l b) := by
  rw [uaVeb hl hX (mxOm2_mem _ _) hbH ldOm2_SC.1.ne' (uaG_le_F hb1) hEG, uaTh_lt tgOm_lt_G, txOm2 hl hX]

/-- **`φ(Ω₂, b + 1)` (`b ≥ 1`): members `φ(c, φ(Ω₂, b) + 1)` indexed by the codes `c`.** -/
theorem uaMB_W {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b)
    (hEG : veblen (Om (1 + 1)) (b + 1) < uaGam) : UaMB S l (veblen (Om (1 + 1)) (b + 1)) := by
  set E := veblen (Om (1 + 1)) (b + 1) with hE_def
  set N := veblen (Om (1 + 1)) b with hN_def
  have hNH : N ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) hbH
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim ldOm2_SC.1.ne'
  have hN1E : N + 1 < E := hElim.add_one_lt hNE
  have hGN : veblen (Om (1 + 1)) 1 ≤ N := uaG_le_F hb1
  have hNG : N < uaGam := hNE.trans hEG
  have hb1G : b + 1 < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTN : uaTh S l N = veblen (Om 1) (uaTh S l b) := uaThF hl hX hbH hb1 hNG
  have hTE : uaTh S l E = veblen (Om 1) (uaTh S l b + 1) := by
    rw [uaThF hl hX (CSet.succ_mem hbH) le_add_self hEG, uaSucc hl hX hbH hb1G]
  have hmE : ∀ c, c < Om (1 + 1) → veblen c (N + 1) < E := fun c hc => by
    calc veblen c (N + 1) < veblen c E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hc _
  refine ⟨fun c => veblen c (N + 1), fun v => veblen v (veblen (Om 1) (uaTh S l b) + 1),
    fun a c h => veblen_left_monotone _ h, fun a c h => veblen_left_monotone _ h, ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc1).ne'
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hGm : veblen (Om (1 + 1)) 1 ≤ veblen c (N + 1) :=
      (hGN.trans (le_self_add : N ≤ N + 1)).trans (right_le_veblen _ _)
    refine ⟨CSet.phi_mem hcH (CSet.succ_mem hNH), Order.one_le_iff_pos.2 veblen_pos, hmE c hcW, ?_, ?_⟩
    · rw [uaVeb hl hX hcH (CSet.succ_mem hNH) hc0 hGm ((hmE c hcW).trans hEG), uaThCode hl hX hcW,
        uaSucc hl hX hNH (hN1E.trans hEG), hTN]
    · rw [hTE]
      refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hΘc, ?_⟩))
      exact (taVeb_lim (Om_pos one_ne_zero).ne').add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one _))
  · intro Q hQ _ w hw hwE
    have hx' : w < veblen (Om (1 + 1)) (b + 1) := hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ ldOm2_SC ldOm2_SC.isSuccLimit w hw hx'
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := tdCl_levDec hQ tnSC1 tnSC1.isSuccLimit w hw hwE
    exact ⟨c', tdCl_lt hQ c' hc' hc'W, hxc'⟩
  · intro Q hQ c h _ hcQ h1 h2 hh
    have hNh : N < h := ((lt_add_one N).trans_le (right_le_veblen c (N + 1))).trans_le h1
    have hNc := uaCl_NW hQ ldOm2_SC hh hNh h2
    exact LeCl.phi (LeCl.small hcQ) (LeCl.add hNc (LeCl.small (gg_one_lt_of_SC hQ)))

/-- **`φ(Ω₂, b)`, `b` a limit with countable members**: the members `φ(Ω₂, m)`. -/
theorem uaMA_Wlim {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hblim : IsSuccLimit b)
    (hEG : veblen (Om (1 + 1)) b < uaGam) (hA : UaMA S l b) : UaMA S l (veblen (Om (1 + 1)) b) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  set E := veblen (Om (1 + 1)) b with hE_def
  have hb1 : 1 ≤ b := (Rv.rvLim_one_lt hblim).le
  have hbG : b < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hmE : ∀ m, Mem m → veblen (Om (1 + 1)) m < E := fun m hm =>
    (veblen_lt_veblen_iff_right).2 (hdat m hm).2.2
  have hTm : ∀ m, Mem m → uaTh S l (veblen (Om (1 + 1)) m) = veblen (Om 1) (uaTh S l m) := fun m hm =>
    uaThF hl hX (hdat m hm).1 (hdat m hm).2.1 ((hmE m hm).trans hEG)
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = veblen (Om (1 + 1)) m, ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    exact ⟨CSet.phi_mem (mxOm2_mem _ _) (hdat m hm).1, Order.one_le_iff_pos.2 veblen_pos, hmE m hm⟩
  · intro y0 hy0H hy0
    by_cases h0 : veblen (Om (1 + 1)) 0 ≤ y0
    swap
    · push Not at h0
      exact ⟨_, ⟨m0, hm0, rfl⟩, h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le)⟩
    obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hy0H h0
    have hub : u < b := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hy0)
    obtain ⟨m, hm, hum⟩ := hA1 u huH hub
    exact ⟨_, ⟨m, hm, rfl⟩, hu2.trans_le ((veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hum))⟩
  · intro w hw
    rw [uaThF hl hX hbH hb1 hEG] at hw
    have hTlim : IsSuccLimit (uaTh S l b) := uaLimT hl hX b hbH hblim hbG
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    obtain ⟨m, hm, hum⟩ := hA2 _ hu'
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 hum)
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
    obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx ldOm2_SC hQ.1 h hh h0
    have hmu : m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
    have hub : u ≤ b := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact LeCl.phi LeCl.om (hA3 Q hQ m u hm hmu hub hu)

/-- **`φ(Ω₂, b)`, `b` a limit with members indexed by the codes**: the members `φ(Ω₂, M c)`. -/
theorem uaMB_Wlim {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hblim : IsSuccLimit b)
    (hEG : veblen (Om (1 + 1)) b < uaGam) (hB : UaMB S l b) : UaMB S l (veblen (Om (1 + 1)) b) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen (Om (1 + 1)) b with hE_def
  have hb1 : 1 ≤ b := (Rv.rvLim_one_lt hblim).le
  have hbG : b < uaGam := (right_le_veblen _ _).trans_lt hEG
  have hTE : uaTh S l E = veblen (Om 1) (uaTh S l b) := uaThF hl hX hbH hb1 hEG
  have hTlim : IsSuccLimit (uaTh S l b) := uaLimT hl hX b hbH hblim hbG
  refine ⟨fun c => veblen (Om (1 + 1)) (M c), fun c => veblen (Om 1) (Mh c),
    fun x y h => (veblen_le_veblen_iff_right).2 (hM h),
    fun x y h => (veblen_le_veblen_iff_right).2 (hMh h), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, hM1, hMb, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    have hlt : veblen (Om (1 + 1)) (M c) < E := (veblen_lt_veblen_iff_right).2 hMb
    refine ⟨CSet.phi_mem (mxOm2_mem _ _) hMH, Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [uaThF hl hX hMH hM1 (hlt.trans hEG), hTM]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 hMhT
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u, hu, hub, hwu⟩ := uaCl_decK hQ ldOm2_SC hblim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u hu hub
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 huc')⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u, hu, hub, hwu⟩ := uaCl_decK hQ Ph.ph_SC_Om1 hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u hu hub
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 huc')⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
    obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx ldOm2_SC hQ.1 h hh h0
    have hmu : M c ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
    have hub : u ≤ b := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact LeCl.phi LeCl.om (hB3 Q hQ c u hc1' hcQ hmu hub hu)

/-- **Every node `φ(Ω₂, b)` (`1 ≤ b`, `φ(Ω₂, b) < Γ₂`) has a member system**, given one for `b` when `b` is a
limit. -/
theorem uaNodeW {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b)
    (hEG : veblen (Om (1 + 1)) b < uaGam) (IH : IsSuccLimit b → UaMA S l b ∨ UaMB S l b) :
    UaMA S l (veblen (Om (1 + 1)) b) ∨ UaMB S l (veblen (Om (1 + 1)) b) := by
  rcases zero_or_succ_or_isSuccLimit b with h0 | ⟨b', hb'⟩ | hbl
  · rw [h0] at hb1; exact absurd hb1 (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hb'
    subst hb'
    have hb'H : b' ∈ cdHull S l := mem_of_add_one_mem hbH
    rcases eq_or_ne b' 0 with rfl | hb'0
    · rw [zero_add]; exact Or.inr (uaMB_G hl hX)
    · exact Or.inr (uaMB_W hl hX hb'H (Order.one_le_iff_ne_zero.2 hb'0) hEG)
  · rcases IH hbl with hA | hB
    · exact Or.inl (uaMA_Wlim hl hX hbH hbl hEG hA)
    · exact Or.inr (uaMB_Wlim hl hX hbH hbl hEG hB)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua
