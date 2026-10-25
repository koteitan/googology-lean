import Googology.Trans.PoR.InaccPsi.R2.UqNode

/-!
# Member systems of the nodes at the level `Ω₂` past `Γ₂`, and the level statement up to `φ(Ω₂ + 1, Γ₂ + 1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q`, `CL₃ = Ug.UgCL`,
`F_b = φ(Ω₂, b)`, `T F_b = φ(Ω₁, T b)`, `Γ₂ = Ua.uaGam = F_{Γ₂} = φ(Ω₂ + 1, Γ₂)`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

`Td.tdCl_levDec`, `Ua.uaCl_decK`, `Ua.uaCl_NW`, `Ua.uaThF`, `Ua.uaMB_W`, `Ua.uaMA_Wlim`, `Ua.uaMB_Wlim`, `Ua.uaNodeW`
past `Γ₂` (level codes, image `T`, bound `Y₃`; an atom `ψ_{Ω_{k+1}}(d)` is strongly critical, so it is treated
like `Ω_k`).

* `uqCl_levDec` (**the fine closure law in the level argument for level codes**), `uqCl_decK`, `uqCl_NW`;
* `uqThF` (`T(φ(Ω₂, b)) = φ(Ω₁, T b)`, `b ≥ 1`), `uqMB_W` (`φ(Ω₂, b + 1)`, `b ≥ Γ₂`), `uqMA_Wlim`, `uqMB_Wlim`
  (`φ(Ω₂, b)`, `b` a limit), `uqNodeW` (**every node `φ(Ω₂, b)`, `Γ₂ < b`, `< Y₃`, has a member system**);
* `uqFix_F2` (a `W`-fixed `r ∈ (Γ₂, φ(Ω₂ + 1, Γ₂ + 1))` is `φ(a, y)` with `1 ≤ a ≤ Ω₂`), `uqFixW2`
  (**`UqFixMS S λ φ(Ω₂ + 1, Γ₂ + 1)` holds**), `uqLevW2` (**UNCONDITIONAL: `UjLev (CL₃ E) E (T E)` AT EVERY LEVEL
  `Ω₂ ≤ E < φ(Ω₂ + 1, Γ₂ + 1)` OF `H_λ`**).

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
  Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Code

variable {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0)

include hQ hk

/-- **THE FINE CLOSURE LAW IN THE LEVEL ARGUMENT FOR LEVEL CODES**: at a limit level `c`, a code `w < φ(c, z+1)` is
below `φ(c', φ(c, z) + 1)` for a code `c' < c`. -/
theorem uqCl_levDec {c z : Ordinal.{0}} (hc : IsSuccLimit c) :
    ∀ w, UgC S k Q w → w < veblen c (z + 1) →
      ∃ c', UgC S k Q c' ∧ c' < c ∧ w < veblen c' (veblen c z + 1) := by
  have hc0 : 0 < c := hc.bot_lt
  have triv : ∀ w, w ≤ veblen c z → ∃ c', UgC S k Q c' ∧ c' < c ∧ w < veblen c' (veblen c z + 1) := by
    intro w hw
    refine ⟨0, UgC.zero hQ.1, hc0, ?_⟩
    exact hw.trans_lt ((lt_add_one _).trans_le (right_le_veblen 0 _))
  -- a strongly critical `s < φ(c, z + 1)` is `≤ φ(c, z)`
  have hSCs : ∀ s, SC s → s < veblen c (z + 1) → s ≤ veblen c z := by
    intro s hs hlt
    rcases lt_or_ge c s with hcs | hsc
    · have hfix : veblen c s = s := hs.veblen_right hcs
      by_contra hcon
      push Not at hcon
      have hzs : z < s := by
        by_contra h'
        push Not at h'
        have := (veblen_le_veblen_iff_right (o := c)).2 h'
        rw [hfix] at this; exact absurd hcon (not_lt.2 this)
      have : veblen c (z + 1) ≤ veblen c s :=
        (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hzs)
      rw [hfix] at this; exact absurd hlt (not_lt.2 this)
    · exact hsc.trans (left_le_veblen c z)
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    rcases le_or_gt w (veblen c z) with h | h
    · exact triv w h
    · obtain ⟨a', ha', hwa⟩ := taVeb_lim_cof hc hlt
      have hcQ : c < Q := ((left_le_veblen c z).trans_lt h).trans hwQ
      exact ⟨a', UgC.small (ha'.trans hcQ), ha', hwa⟩
  | om => exact fun hlt => triv _ (hSCs _ (SC_Om hk) hlt)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · refine ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · refine ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmcl : UgC S k Q m := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, UgC.add hmcl (UgC.small (gg_one_lt_of_SC hQ)), hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) (veblen c z + 1) :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) (veblen c z + 1)) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) (veblen c z + 1) := veblen_veblen_of_lt hpm _
    · refine triv _ ((veblen_le_veblen_iff_right).2 ?_)
      exact Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
    · refine triv _ ?_
      have hfix : veblen c (veblen p q) = veblen p q := veblen_veblen_of_lt hpc q
      rw [← hfix] at hlt
      have h1 := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
      exact h1.trans (right_le_veblen c z)
  | @psi d hd hdl _ => exact fun hlt => triv _ (hSCs _ (SC_psi (InR_Om_succ k) d) hlt)

/-- **A level code `w < φ(Ω_k, X)` (`X` a limit) is below `φ(Ω_k, u)` for a code `u < X`.** -/
theorem uqCl_decK {X : Ordinal.{0}} (hX : IsSuccLimit X) :
    ∀ w, UgC S k Q w → w < veblen (Om k) X → ∃ u, UgC S k Q u ∧ u < X ∧ w < veblen (Om k) u := by
  have hκ : SC (Om k) := SC_Om hk
  intro w hw hwX
  have h1X : 1 < X := Rv.rvLim_one_lt hX
  rcases lt_or_ge w (Om k) with hwκ | hκw
  · refine ⟨1, UgC.small (gg_one_lt_of_SC hQ), h1X, hwκ.trans_le ?_⟩
    calc Om k = veblen (Om k) 0 := hκ.veblen_zero.symm
      _ ≤ veblen (Om k) 1 := (veblen_le_veblen_iff_right).2 zero_le
  · obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ hk w hw (by rw [hκ.veblen_zero]; exact hκw)
    have huX : u < X := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hwX)
    exact ⟨u + 1, UgC.add hu (UgC.small (gg_one_lt_of_SC hQ)), hX.add_one_lt huX, hu2⟩

omit hk in
/-- **The own transfer at the level `Ω₂`**: a level-2 code `h` with `φ(Ω₂, b) < h ≤ φ(Ω₂, b + 1)` gives the code
`φ(Ω₂, b)`. -/
theorem uqCl_NW {b h : Ordinal.{0}} (hh : UgC S (1 + 1) Q h) (h1 : veblen (Om (1 + 1)) b < h)
    (h2 : h ≤ veblen (Om (1 + 1)) (b + 1)) : UgC S (1 + 1) Q (veblen (Om (1 + 1)) b) := by
  have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
  have hbu : b ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ b + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact UgC.phi UgC.om (uqCl_of_succ hQ hbu hhi hu)

end Code

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T(φ(Ω₂, b)) = φ(Ω₁, T b)` for `b ≥ 1` (`φ(Ω₂, b) < Y₃`). -/
theorem uqThF {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hb1 : 1 ≤ b) (hY : veblen (Om (1 + 1)) b < ugY S) :
    ugTh S l (veblen (Om (1 + 1)) b) = veblen (Om 1) (ugTh S l b) := by
  rcases lt_or_ge (veblen (Om (1 + 1)) b) uaGam with h | h
  · rw [ugTh_lt h, uaThF hl hX hbH hb1 h, ugTh_lt ((right_le_veblen _ _).trans_lt h)]
  · rw [ugVeb hl hX (mxOm2_mem _ _) hbH ldOm2_SC.1.ne' h hY, ugTh_lt uaGam_spec.2, uaTh_lt tgOm_lt_G,
      txOm2 hl hX]

/-- **`φ(Ω₂, b + 1)` (`Γ₂ ≤ b`): members `φ(c, φ(Ω₂, b) + 1)` indexed by the codes `c`.** -/
theorem uqMB_W {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hGb : uaGam ≤ b)
    (hEY : veblen (Om (1 + 1)) (b + 1) < ugY S) : UqMB S l (veblen (Om (1 + 1)) (b + 1)) := by
  set E := veblen (Om (1 + 1)) (b + 1) with hE_def
  set N := veblen (Om (1 + 1)) b with hN_def
  have hb1 : 1 ≤ b := (gg_one_lt_of_SC uaGam_spec.1).le.trans hGb
  have hNH : N ∈ cdHull S l := CSet.phi_mem (mxOm2_mem _ _) hbH
  have hNE : N < E := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hElim : IsSuccLimit E := taVeb_lim ldOm2_SC.1.ne'
  have hN1E : N + 1 < E := hElim.add_one_lt hNE
  have hGN : uaGam ≤ N := uqGam_le_F hGb
  have hNY : N < ugY S := hNE.trans hEY
  have hb1Y : b + 1 < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hTN : ugTh S l N = veblen (Om 1) (ugTh S l b) := uqThF hl hX hbH hb1 hNY
  have hTE : ugTh S l E = veblen (Om 1) (ugTh S l b + 1) := by
    rw [uqThF hl hX (CSet.succ_mem hbH) le_add_self hEY, ugSucc hl hX hbH hb1Y]
  have hmE : ∀ c, c < Om (1 + 1) → veblen c (N + 1) < E := fun c hc => by
    calc veblen c (N + 1) < veblen c E := (veblen_lt_veblen_iff_right).2 hN1E
      _ = E := veblen_veblen_of_lt hc _
  refine ⟨fun c => veblen c (N + 1), fun v => veblen v (veblen (Om 1) (ugTh S l b) + 1),
    fun a c h => veblen_left_monotone _ h, fun a c h => veblen_left_monotone _ h, ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hc0 : c ≠ 0 := (zero_lt_one.trans_le hc1).ne'
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hGm : uaGam ≤ veblen c (N + 1) := (hGN.trans (le_self_add : N ≤ N + 1)).trans (right_le_veblen _ _)
    refine ⟨CSet.phi_mem hcH (CSet.succ_mem hNH), Order.one_le_iff_pos.2 veblen_pos, hmE c hcW, ?_, ?_⟩
    · rw [ugVeb hl hX hcH (CSet.succ_mem hNH) hc0 hGm ((hmE c hcW).trans hEY), uqThCode hl hX hcW,
        ugSucc hl hX hNH (hN1E.trans hEY), hTN]
    · rw [hTE]
      refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hΘc, ?_⟩))
      exact (taVeb_lim (Om_pos one_ne_zero).ne').add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one _))
  · intro Q hQ _ w hw hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := uqCl_levDec hQ ugTwo_ne ldOm2_SC.isSuccLimit w hw hwE
    exact ⟨c', ugC_lt_om hQ hc' hc'W, hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨c', hc', hc'W, hxc'⟩ := uqCl_levDec hQ one_ne_zero (SC_Om one_ne_zero).isSuccLimit w hw hwE
    exact ⟨c', ugC_lt_om hQ hc' hc'W, hxc'⟩
  · intro Q hQ c h _ hcQ h1 h2 hh
    have hNh : N < h := ((lt_add_one N).trans_le (right_le_veblen c (N + 1))).trans_le h1
    have hNc := uqCl_NW hQ hh hNh h2
    exact UgC.phi (UgC.small hcQ) (UgC.add hNc (UgC.small (gg_one_lt_of_SC hQ)))

/-- **`φ(Ω₂, b)`, `b` a limit with countable members**: the members `φ(Ω₂, m)`. -/
theorem uqMA_Wlim {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hblim : IsSuccLimit b)
    (hEY : veblen (Om (1 + 1)) b < ugY S) (hA : UqMA S l b) : UqMA S l (veblen (Om (1 + 1)) b) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  set E := veblen (Om (1 + 1)) b with hE_def
  have hb1 : 1 ≤ b := (Rv.rvLim_one_lt hblim).le
  have hbY : b < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hmE : ∀ m, Mem m → veblen (Om (1 + 1)) m < E := fun m hm =>
    (veblen_lt_veblen_iff_right).2 (hdat m hm).2.2
  have hTm : ∀ m, Mem m → ugTh S l (veblen (Om (1 + 1)) m) = veblen (Om 1) (ugTh S l m) := fun m hm =>
    uqThF hl hX (hdat m hm).1 (hdat m hm).2.1 ((hmE m hm).trans hEY)
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
    rw [uqThF hl hX hbH hb1 hEY] at hw
    have hTlim : IsSuccLimit (ugTh S l b) := uqLimT hl hX b hbH hblim hbY
    obtain ⟨u', hu', hwu⟩ := ((isNormal_veblen _).lt_iff_exists_lt hTlim).1 hw
    obtain ⟨m, hm, hum⟩ := hA2 _ hu'
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    exact hwu.trans ((veblen_lt_veblen_iff_right).2 hum)
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
    obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
    have hmu : m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
    have hub : u ≤ b := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact UgC.phi UgC.om (hA3 Q hQ m u hm hmu hub hu)

/-- **`φ(Ω₂, b)`, `b` a limit with members indexed by the codes**: the members `φ(Ω₂, M c)`. -/
theorem uqMB_Wlim {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hblim : IsSuccLimit b)
    (hEY : veblen (Om (1 + 1)) b < ugY S) (hB : UqMB S l b) : UqMB S l (veblen (Om (1 + 1)) b) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  set E := veblen (Om (1 + 1)) b with hE_def
  have hb1 : 1 ≤ b := (Rv.rvLim_one_lt hblim).le
  have hbY : b < ugY S := (right_le_veblen _ _).trans_lt hEY
  have hTE : ugTh S l E = veblen (Om 1) (ugTh S l b) := uqThF hl hX hbH hb1 hEY
  have hTlim : IsSuccLimit (ugTh S l b) := uqLimT hl hX b hbH hblim hbY
  refine ⟨fun c => veblen (Om (1 + 1)) (M c), fun c => veblen (Om 1) (Mh c),
    fun x y h => (veblen_le_veblen_iff_right).2 (hM h),
    fun x y h => (veblen_le_veblen_iff_right).2 (hMh h), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, hM1, hMb, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    have hlt : veblen (Om (1 + 1)) (M c) < E := (veblen_lt_veblen_iff_right).2 hMb
    refine ⟨CSet.phi_mem (mxOm2_mem _ _) hMH, Order.one_le_iff_pos.2 veblen_pos, hlt, ?_, ?_⟩
    · rw [uqThF hl hX hMH hM1 (hlt.trans hEY), hTM]
    · rw [hTE]; exact (veblen_lt_veblen_iff_right).2 hMhT
  · intro Q hQ hQ1 w hw hwE
    obtain ⟨u, hu, hub, hwu⟩ := uqCl_decK hQ ugTwo_ne hblim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB1 Q hQ hQ1 u hu hub
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 huc')⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    obtain ⟨u, hu, hub, hwu⟩ := uqCl_decK hQ one_ne_zero hTlim w hw hwE
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ u hu hub
    exact ⟨c', hc'Q, hwu.trans ((veblen_lt_veblen_iff_right).2 huc')⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
    obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
    have hmu : M c ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
    have hub : u ≤ b := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact UgC.phi UgC.om (hB3 Q hQ c u hc1' hcQ hmu hub hu)

/-- **Every node `φ(Ω₂, b)` with `Γ₂ < b`, `φ(Ω₂, b) < Y₃`, has a member system**, given one for `b` when `b` is
a limit. -/
theorem uqNodeW {b : Ordinal.{0}} (hbH : b ∈ cdHull S l) (hGb : uaGam < b)
    (hEY : veblen (Om (1 + 1)) b < ugY S) (IH : IsSuccLimit b → UqMA S l b ∨ UqMB S l b) :
    UqMA S l (veblen (Om (1 + 1)) b) ∨ UqMB S l (veblen (Om (1 + 1)) b) := by
  rcases zero_or_succ_or_isSuccLimit b with h0 | ⟨b', hb'⟩ | hbl
  · rw [h0] at hGb; exact absurd hGb (not_lt.2 zero_le)
  · rw [succ_eq_add_one] at hb'
    subst hb'
    have hb'H : b' ∈ cdHull S l := mem_of_add_one_mem hbH
    exact Or.inr (uqMB_W hl hX hb'H (Order.lt_add_one_iff.1 hGb) hEY)
  · rcases IH hbl with hA | hB
    · exact Or.inl (uqMA_Wlim hl hX hbH hbl hEY hA)
    · exact Or.inr (uqMB_Wlim hl hX hbH hbl hEY hB)

omit hl hX in
/-- **A fixed point of `φ(Ω₂, ·)` above `Γ₂` is `≥ φ(Ω₂ + 1, Γ₂ + 1)`.** -/
theorem uqFfix_next {r : Ordinal.{0}} (hfix : veblen (Om (1 + 1)) r = r) (hGr : uaGam < r) :
    veblen (Om (1 + 1) + 1) (uaGam + 1) ≤ r := by
  -- `r` is a fixed point of `φ(Ω₂, ·)`, so a value of its derivative `φ(Ω₂ + 1, ·)`
  obtain ⟨β, hβ⟩ : ∃ β, veblen (Om (1 + 1) + 1) β = r := by
    rw [veblen_add_one]; exact (mem_range_deriv (isNormal_veblen _)).2 hfix
  have hG : veblen (Om (1 + 1) + 1) uaGam = uaGam :=
    uaGam_spec.1.veblen_right (uaGam_spec.1.isSuccLimit.add_one_lt uaGam_spec.2)
  have hGβ : uaGam < β := by
    rw [← hβ, ← hG] at hGr; exact (veblen_lt_veblen_iff_right).1 hGr
  rw [← hβ]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hGβ)

omit hl hX in
/-- `φ(Ω₂ + 1, Γ₂ + 1) < Y₃`. -/
theorem uqFW2_lt_Y : veblen (Om (1 + 1) + 1) (uaGam + 1) < ugY S :=
  uqY_SC.2 _ (uqY_SC.isSuccLimit.add_one_lt uqW_lt_Y) _ (uqY_SC.isSuccLimit.add_one_lt ujGam_lt_Y)

/-- **`UqFixMS S λ φ(Ω₂ + 1, Γ₂ + 1)`**: `Γ₂` by the members `X_k`, the window nodes with a code level by
`uqNodeMS`, the nodes `φ(Ω₂, b)` by `uqNodeW`; no fixed point of `φ(Ω₂, ·)` lies in `(Γ₂, φ(Ω₂ + 1, Γ₂ + 1))`. -/
theorem uqFixW2 : UqFixMS S l (veblen (Om (1 + 1) + 1) (uaGam + 1)) := by
  intro r hrH hGr hrB hrs IH
  rcases hGr.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact Or.inl (uqMA_gam hl hX)
  have hrY : r < ugY S := hrB.trans uqFW2_lt_Y
  have hnofix : veblen (Om (1 + 1)) r ≠ r := fun h => absurd (uqFfix_next h hlt) (not_le.2 hrB)
  have hS : ¬ SC r := fun hS => hnofix (hS.veblen_right (uaGam_spec.2.trans hlt))
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := ugNode hlt.le hS hrs
  set a := invVeblen₁ r with ha_def
  set y := invVeblen₂ r with hy_def
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  rcases lt_trichotomy a (Om (1 + 1)) with haW | haW | haW
  · -- a code level: the window of `r`
    have hΩr : veblen (Om (1 + 1)) 0 ≤ r := by
      rw [ldOm2_SC.veblen_zero]; exact (uaGam_spec.2.trans hlt).le
    obtain ⟨u, huH, hu1', hu2'⟩ := txHull_idx hrH hΩr
    have hne : veblen (Om (1 + 1)) u ≠ r := by
      intro he
      have hfix : veblen a r = r := by rw [← he]; exact veblen_veblen_of_lt haW _
      have : y = r := by
        have h2 : veblen a y = veblen a r := by rw [hv, hfix]
        exact veblen_injective a h2
      exact absurd (this ▸ hbE) (lt_irrefl _)
    have hGu : uaGam ≤ u := by
      by_contra hc
      push Not at hc
      have h1 : veblen (Om (1 + 1)) (u + 1) ≤ veblen (Om (1 + 1)) uaGam :=
        (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hc)
      rw [uaGam_spec.1.veblen_right uaGam_spec.2] at h1
      exact absurd (hu2'.trans_le h1) (not_lt.2 hlt.le)
    have h := uqNodeMS hl hX hGu huH hmem.1 (Order.one_le_iff_pos.2 ha0) haW hmem.2
      (by rw [hv]; exact lt_of_le_of_ne hu1' hne) (by rw [hv]; exact hu2') (by rw [hv]; exact hrY)
      (fun hyl => IH _ hmem.2 hyl hbE)
    rwa [hv] at h
  · -- the level `Ω₂`
    have hGy : uaGam < y := by
      have hFG : veblen (Om (1 + 1)) uaGam = uaGam := uaGam_spec.1.veblen_right uaGam_spec.2
      rw [← hv, haW, ← hFG] at hlt
      exact (veblen_lt_veblen_iff_right).1 hlt
    have h := uqNodeW hl hX hmem.2 hGy (by rw [← haW, hv]; exact hrY) (fun hyl => IH _ hmem.2 hyl hbE)
    rwa [← haW, hv] at h
  · exact absurd (by rw [← hv]; exact veblen_veblen_of_lt haW _) hnofix

/-- **UNCONDITIONAL: THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < φ(Ω₂ + 1, Γ₂ + 1)` OF `H_λ`** (image
`T E`, own predicate `CL₃ E`). -/
theorem uqLevW2 {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < veblen (Om (1 + 1) + 1) (uaGam + 1)) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevB hl hX (uqFixW2 hl hX) uqFW2_lt_Y.le (taVeb_lim (zero_lt_one.trans_le le_add_self).ne') hEH hWE hE

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
