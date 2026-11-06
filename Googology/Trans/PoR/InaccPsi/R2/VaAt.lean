import Googology.Trans.PoR.InaccPsi.R2.VaCu

/-!
# VaAt: THE TOP DATA AT AN ATOM BASE `Γ(j)`, `B_Γ < j < Γ(j) < B₂`

The atom `E = Γ(j)` reads `gq(I(x)) x`, `I(x) = D(x) + o(x)`, `o = j − (B_Γ+1)` (`Va.vI`).  The codes below `E` read
below it (`gq(I(x))` is closed under `ϑˣ(Ω₁·α + η)`, under the smaller atoms and under the ordinal operations), and
their readings are cofinal in it: at `o = 0` and at a successor `o` their supremum would be strongly critical between
`gq(c)` and `gq(c+1)` (`Xk.xk_sc_iff`), at a limit `o` the index reading is a limit and not closed
(`Va.va_nonclosed`) so `ν ↦ gq ν x` is continuous there (`Zb.zb_lt_lim_iff`).

* `va_sub_lt`, `va_idx_lt`, `va_at_gate`, `va_at_I`, `va_lt_at`, `va_top_at`;
* `vaTopAt` (**THE TOP DATA AT AN ATOM**), `vaGood_all2` (**`VaGood E` for every `ε`-number `B_Γ ≤ E < B₂`**).

No new axiom.  New definition: `vaTopAt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge

theorem va_sub_lt {j' j : Ordinal.{0}} (h1 : tfBG + 1 ≤ j') (h : j' < j) :
    j' - (tfBG + 1) < j - (tfBG + 1) := by
  obtain ⟨o', rfl⟩ := exists_add_of_le h1
  obtain ⟨o, rfl⟩ := exists_add_of_le (h1.trans h.le)
  rw [Ordinal.add_sub_cancel, Ordinal.add_sub_cancel]; exact (add_lt_add_iff_left _).1 h

/-- **An atom index past `B_Γ` below `B₂` is below its atom.** -/
theorem va_idx_lt {i : Ordinal.{0}} (hi : tfBG < i) (hiB : gcG i < vaB2) : i < gcG i := by
  have hBi : tfBG ≤ gcG i := by rw [← zb_gcG_BG]; exact gcG_le hi.le
  rcases va_atom_cases2 hBi hiB with h | ⟨-, -, h⟩ | h
  · rw [← zb_gcG_BG] at h; exact absurd (gcG_strictMono.injective h) hi.ne'
  · rwa [yhJ_gcG] at h
  · exact absurd (yhAt_gcG i) h

section Atom

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEU : E < vaB2)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → VaGood e)
  (hA : YhAt E) (hjB : tfBG < yhJ E) (hjE : yhJ E < E)
  {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)

include hA hjE in
theorem va_at_E : gcG (yhJ E) = E := by
  obtain ⟨j0, rfl⟩ := yhAt_iff.1 hA; rw [yhJ_gcG]

include hjE in
theorem va_at_o : yhJ E - (tfBG + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hjE

include hA hjB hjE hx in
theorem va_at_gate (hgx : max ω (yrQE E) < x) : yrG (yhJ E) < x ∧ yrG (yhJ E - (tfBG + 1)) < x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hQ : yrQE E = yrQ (yhJ E) := yrQE_atom hA hjE
  have hgj : yrG (yhJ E) < x := yrG_of_Q hωx (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgx)
  exact ⟨hgj, (va_off_gate hjB).trans_lt (max_lt hωx hgj)⟩

include hE hBE hEU hlim hIH hA hjB hjE hx hx1

/-- **The index reading of the atom.** -/
theorem va_at_I (hgx : max ω (yrQE E) < x) :
    ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x ∈ Tset x ∧ ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x < Om1 ∧
      ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x < ywV 1 1 x := by
  obtain ⟨-, hgo⟩ := va_at_gate hA hjB hjE hx hgx
  obtain ⟨-, -, hoD2⟩ := va_T hE hBE hEU hlim hIH hx hx1 (va_at_o hjE) hgo
  obtain ⟨hDD2, hD2T, hD21, hD2E, -⟩ := va_D2_facts hx hx1
  have hI : ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x < ywV 1 1 x := (inE_indec hD2E).add_lt hDD2 hoD2
  exact ⟨vz_T_down hx hx1 hD2T hD21 hI.le, hI.trans hD21, hI⟩

/-- **Every code below the atom reads below `gq(I(x))`.** -/
theorem va_lt_at (hgx : max ω (yrQE E) < x) :
    ∀ c, c < E → yrG c < x → vR c x < gq (ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x) x := by
  have hωx : ω < x := omega0_lt_inE hx
  obtain ⟨hgj, hgo⟩ := va_at_gate hA hjB hjE hx hgx
  obtain ⟨hIT, hI1, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
  set I := ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x with hIdef
  obtain ⟨hqT, hxq, hq1, hqE, -⟩ := geq_facts hx hx1 hIT hI1
  have hDq : ywV 1 0 x < gq I x := le_self_add.trans_lt (gmq_gt hx hx1 hIT hI1)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  by_cases hcB : c < tfBG
  · rw [vR_yr c hcB x]; exact (zmYr.lt c x hx hx1 hcB hg).trans hDq
  have hcB' : tfBG ≤ c := not_lt.1 hcB
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hcB'
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hGc)
  have hg0 := hg
  rw [yrG_dec hGc] at hg
  have hgQE : yrQE (guE c) < x := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgk : yrG (log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg))
  have hgd : yrG (c / guE c ^ log (guE c) c) < x :=
    yrG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg))
  have hgr : yrG (c % guE c ^ log (guE c) c) < x := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hcB'
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hA' : vA (guE c) x < gq I x := by
    rcases va_atom_cases2 heB ((hec.trans_lt hc).trans hEU) with hB | ⟨hAc, hjB', hjE'⟩ | hnA
    · rw [hB, vA_BG]; exact hDq
    · -- a smaller atom `Γ(j')`: `j' < j`
      rw [vA_atom hAc hjE', vI_high hjB']
      have hj'j : yhJ (guE c) < yhJ E := by
        have h := hec.trans_lt hc
        rw [← va_at_E hAc hjE', ← va_at_E hA hjE] at h
        exact gcG_strictMono.lt_iff_lt.1 h
      have hgj' : yrG (yhJ (guE c)) < x := by
        rw [yrQE_atom hAc hjE'] at hgQE; exact yrG_of_Q hωx hgQE
      have hgo' := (va_off_gate hjB').trans_lt (max_lt hωx hgj')
      have hlt := va_mono hE hBE hEU hlim hIH hx hx1 (va_sub_lt (Order.add_one_le_of_lt hjB') hj'j)
        (va_at_o hjE) hgo' hgo
      exact gmq_lt hx hx1 hIT hI1 ((add_lt_add_iff_left _).2 hlt)
    · rw [vA_psi hnA]
      have hK := yh_lev_lt hGc hnA
      have hI' := yh_idx_lt hGc hnA
      rw [yrQE_psi hnA] at hgQE
      exact xkA_lt hx hx1 hIT hI1 (IH _ hK (hK.trans hc) (yrG_of_Q hωx ((le_max_left _ _).trans_lt hgQE)))
        (IH _ hI' (hI'.trans hc) (yrG_of_Q hωx ((le_max_right _ _).trans_lt hgQE)))
  rw [vR_dec hGc]
  exact (inE_indec hqE).add_lt (InE.mul_lt hqE (zm_opow_lt hqE hA' (IH _ hlog (hlog.trans hc) hgk))
    (IH _ hdiv (hdiv.trans hc) hgd)) (IH _ hmod (hmod.trans hc) hgr)

omit hx hx1 in
/-- The top bound as a function of the base. -/
theorem va_ltTat : ∀ y, InE y → y < Om1 → max ω (yrQE E) < y → ∀ c, c < E → yrG c < y →
    vR c y < vA E y := by
  intro y hy hy1 hgy c hc hg
  rw [vA_atom hA hjE, vI_high hjB]
  exact va_lt_at hE hBE hEU hlim hIH hA hjB hjE hy hy1 hgy c hc hg

/-- **The readings of the codes below the atom are cofinal in `gq(I(x))`.** -/
theorem va_top_at (hgx : max ω (yrQE E) < x) :
    ∀ ν, ν < gq (ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x) x → ∃ b, b < E ∧ yrG b < x ∧ ν ≤ vR b x := by
  have hωx : ω < x := omega0_lt_inE hx
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  have hEl : IsSuccLimit E := ev_isSuccLimit_of_inE hE
  have hxP : ∀ u v, u < x → v < x → u + v < x := fun u v hu hv => (inE_indec hx).add_lt hu hv
  obtain ⟨hgj, hgo⟩ := va_at_gate hA hjB hjE hx hgx
  have hoE := va_at_o hjE
  obtain ⟨hIT, hI1, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
  obtain ⟨hDT, hxD, hD1, hDE⟩ := zmD_facts hx hx1
  obtain ⟨-, -, hDcl⟩ := ywD_closed hx hx1
  have hGE : gcG 0 < E := va_G_le_BG.trans_lt hBE
  have hgB : yrG tfBG < x := by
    rw [yrG_base (Low.opow_eq_self_of_SC tfBG_SC) va_G_le_BG, va_QE_BG]; exact hx.pos
  have hgG : yrG (gcG 0) < x := by rw [yrG_G0]; exact hx.pos
  -- the atoms `Γ(B_Γ + 1 + b)` below `E`
  have hatom : ∀ b, b < yhJ E - (tfBG + 1) → yrG b < x →
      gcG (tfBG + 1 + b) < E ∧ yrG (gcG (tfBG + 1 + b)) < x ∧
        vR (gcG (tfBG + 1 + b)) x = gq (ywV 1 0 x + vR b x) x := by
    intro b hb hgb
    have hjb : tfBG + 1 + b < yhJ E := by
      have := (add_lt_add_iff_left (tfBG + 1)).2 hb
      rwa [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hjB)] at this
    have hbE : gcG (tfBG + 1 + b) < E := by rw [← va_at_E hA hjE]; exact gcG_lt hjb
    have hB1 : tfBG < tfBG + 1 + b := (lt_add_one _).trans_le le_self_add
    have hii := va_idx_lt hB1 (hbE.trans hEU)
    have hg1 : yrG (tfBG + 1 + b) < x := by
      have h1 : yrG (1 : Ordinal.{0}) < x := by
        rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate]
        exact (natCast_lt_omega0 1).trans hωx
      exact yr_add hxP hωx _ _ (yr_add hxP hωx _ _ hgB h1) hgb
    refine ⟨hbE, by rw [yrG_atom hii]; exact (yrQ_le _).trans_lt hg1, ?_⟩
    rw [vR_atom hii, vI_high hB1, Ordinal.add_sub_cancel]
  intro ν hν
  by_contra hcon
  push Not at hcon
  set S : Set Ordinal.{0} := {s | ∃ b, b < E ∧ yrG b < x ∧ s = vR b x} with hSdef
  have hSne : S.Nonempty := ⟨vR 0 x, 0, hE.pos, by rw [yrG_zero]; exact hx.pos, rfl⟩
  have hSbdd : BddAbove S := ⟨ν, fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le⟩
  set u := sSup S with hudef
  have hu1 : ∀ b, b < E → yrG b < x → vR b x < u := by
    intro b hb hg
    have h1 : vR (b + 1) x ≤ u := le_csSup hSbdd ⟨b + 1, hEl.add_one_lt hb, yrG_succ hxl b hg, rfl⟩
    rw [vR_succ] at h1
    exact (lt_add_one _).trans_le h1
  have hu2 : u ≤ ν := csSup_le hSne fun s ⟨b, hb, hg, hs⟩ => hs ▸ (hcon b hb hg).le
  have hDu : ywV 1 0 x < u := by have h := hu1 tfBG hBE hgB; rwa [vR_BG] at h
  have hxu : x < u := hxD.trans hDu
  -- `u` is strongly critical
  have hSC : SC u := by
    refine ⟨hx.pos.trans hxu, fun a ha b hb => ?_⟩
    obtain ⟨w1, ⟨t1, ht1, hgt1, rfl⟩, hat1⟩ := exists_lt_of_lt_csSup hSne ha
    obtain ⟨w2, ⟨t2, ht2, hgt2, rfl⟩, hbt2⟩ := exists_lt_of_lt_csSup hSne hb
    set t2' := max t2 (gcG 0) with ht2'
    have ht2E : t2' < E := max_lt ht2 hGE
    have hgt2' : yrG t2' < x := by
      rcases le_total t2 (gcG 0) with h | h
      · rw [ht2', max_eq_right h]; exact hgG
      · rw [ht2', max_eq_left h]; exact hgt2
    have hbt2' : b < vR t2' x := hbt2.trans_le (va_le_mono hE hBE hEU hlim hIH hx hx1 (le_max_left _ _) ht2E hgt2 hgt2')
    have ht10 : t1 ≠ 0 := by rintro rfl; rw [vR_zero] at hat1; exact absurd hat1 (not_lt.2 zero_le)
    have ht11 : 1 ≤ t1 := one_le_iff_ne_zero.2 ht10
    obtain ⟨hT1, h11, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 ht1 hgt1
    obtain ⟨hT2, h12, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 ht2E hgt2'
    have hR1 : 1 ≤ vR t1 x := by
      have h := va_le_mono hE hBE hEU hlim hIH hx hx1 ht11 ht1
        (by rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, va_nat_gate];
            exact (natCast_lt_omega0 1).trans hωx) hgt1
      rwa [vR_one] at h
    have hGp : gcG 0 < yhPsi t1 t2' := (le_max_right _ _).trans_lt (lt_yhPsi t1 t2')
    have hpE : yhPsi t1 t2' < E := yhPsi_lt_SC hA.1 hA.2 ht1 ht2E
    have hgp : yrG (yhPsi t1 t2') < x := by
      rw [yrG_psi ht11 hGp]; exact max_lt ((yrQ_le _).trans_lt hgt1) ((yrQ_le _).trans_lt hgt2')
    calc veblen a b < veblen a (vR t2' x) := veblen_lt_veblen_iff_right.2 hbt2'
      _ ≤ veblen (vR t1 x) (vR t2' x) := veblen_left_monotone _ hat1.le
      _ ≤ glA (vR t1 x) (vR t2' x) x := glA_veb_le hx hx1 hR1 hT1 h11 hT2 h12
      _ = vR (yhPsi t1 t2') x := (vR_psi ht11 hGp x).symm
      _ < u := hu1 _ hpE hgp
  have hveb : veblen u 0 = u := Xf.xf_sc_veb0 hSC
  rcases zero_or_succ_or_isSuccLimit (yhJ E - (tfBG + 1)) with ho0 | ⟨o', ho'⟩ | hol
  · -- `o = 0`: the index reading is `D(x)`
    rw [ho0, vR_zero, add_zero] at hν
    obtain ⟨hD1T, hD11⟩ := gl_T_succ hx hx1 hDT hD1
    have hu3 : u < gq (ywV 1 0 x + 1) x := hu2.trans_lt (hν.trans (gmq_lt hx hx1 hD1T hD11 (lt_add_one _)))
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hDT hD1 hxu hDu hu3).1 hveb
    rcases hc'.lt_or_eq with h | h
    · have := hDcl c' (vz_T_down hx hx1 hDT hD1 hc') h
      rw [hc'u] at this; exact absurd hDu (not_lt.2 this.le)
    · rw [h] at hc'u; rw [← hc'u] at hu2; exact absurd hν (not_lt.2 hu2)
  · -- `o = o' + 1`
    rw [Order.succ_eq_add_one] at ho'
    have ho'o : o' < yhJ E - (tfBG + 1) := by rw [← ho']; exact lt_add_one o'
    have hgo' : yrG o' < x := (yrG_le_succ o').trans_lt (by rw [ho']; exact hgo)
    obtain ⟨hbE, hgb, hrb⟩ := hatom o' ho'o hgo'
    obtain ⟨hcT, hc1, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨ho'T, ho'1, -⟩ := va_T hE hBE hEU hlim hIH hx hx1 (ho'o.trans hoE) hgo'
    obtain ⟨hDD2, hD2T, hD21, hD2E, -⟩ := va_D2_facts hx hx1
    have hcD2 : ywV 1 0 x + vR o' x < ywV 1 1 x :=
      (inE_indec hD2E).add_lt hDD2 (va_T hE hBE hEU hlim hIH hx hx1 (ho'o.trans hoE) hgo').2.2
    have hcT' := vz_T_down hx hx1 hD2T hD21 hcD2.le
    have hcu : gq (ywV 1 0 x + vR o' x) x < u := by rw [← hrb]; exact hu1 _ hbE hgb
    have hIe : ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x = ywV 1 0 x + vR o' x + 1 := by
      rw [← ho', vR_succ, add_assoc]
    rw [hIe] at hν
    have hu3 : u < gq (ywV 1 0 x + vR o' x + 1) x := hu2.trans_lt hν
    obtain ⟨c', hc', hc'u⟩ := (xk_sc_iff hx hx1 hcT' (hcD2.trans hD21) hxu
      ((gmq_gt hx hx1 hcT' (hcD2.trans hD21)).trans hcu) hu3).1 hveb
    have := gmq_mono hx hx1 hcT' (hcD2.trans hD21) hc'
    rw [hc'u] at this
    exact absurd hcu (not_lt.2 this)
  · -- a limit `o`: the index reading is a limit and not closed
    obtain ⟨M, hoM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH
      (va_ltTat hE hBE hEU hlim hIH hA hjB hjE) hoE
    have hGo := va_memG hωx hEg hgo hG hoM hgo
    have hRl : IsSuccLimit (vR (yhJ E - (tfBG + 1)) x) := by
      rw [← hR _ hoM x hx hx1 hGo]; exact M.lim _ x hx hx1 hol hoM hGo
    have hIl : IsSuccLimit (ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x) := isSuccLimit_add _ hRl
    have hDI : ywV 1 0 x < ywV 1 0 x + vR (yhJ E - (tfBG + 1)) x := lt_add_of_pos_right _ hRl.bot_lt
    obtain ⟨hIT', hI1', hID2⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨σ, -, -, hσI, hIσ⟩ := va_nonclosed hx hx1 hIT' hDI hID2
    obtain ⟨ν', hν'I, hνν'⟩ := zb_lt_lim_iff hx hx1 hIl hIT' hI1' ⟨σ, hσI, hIσ⟩ ν hν
    rcases lt_or_ge ν' (ywV 1 0 x) with hν'D | hν'D
    · have h1 := hDcl ν' (vz_T_down hx hx1 hDT hD1 hν'D.le) hν'D
      have h2 := hcon tfBG hBE hgB
      rw [vR_BG] at h2
      exact absurd (hνν'.trans h1) (not_lt.2 h2.le)
    · obtain ⟨δ, rfl⟩ := exists_add_of_le hν'D
      have hδ : δ < vR (yhJ E - (tfBG + 1)) x := (add_lt_add_iff_left _).1 hν'I
      obtain ⟨b', hb', hgb', hδb⟩ := va_below hE hBE hEU hlim hIH hx hx1 hoE hol.bot_lt.ne' hgo δ hδ
      obtain ⟨hbE, hgb, hrb⟩ := hatom b' hb' hgb'
      obtain ⟨hDD2, hD2T, hD21, hD2E, -⟩ := va_D2_facts hx hx1
      have hcD2 : ywV 1 0 x + vR b' x < ywV 1 1 x :=
        (inE_indec hD2E).add_lt hDD2 (va_T hE hBE hEU hlim hIH hx hx1 (hb'.trans hoE) hgb').2.2
      have h1 : gq (ywV 1 0 x + δ) x ≤ gq (ywV 1 0 x + vR b' x) x :=
        gmq_mono hx hx1 (vz_T_down hx hx1 hD2T hD21 hcD2.le) (hcD2.trans hD21) ((add_le_add_iff_left _).2 hδb)
      have h2 := hcon _ hbE hgb
      rw [hrb] at h2
      exact absurd (hνν'.trans_le h1) (not_lt.2 h2.le)

/-- **THE TOP DATA AT AN ATOM.** -/
noncomputable def vaTopAt : VaTop E where
  Ei := E
  W := vA E
  E_eq := hA.1.veblen_right (gg_one_lt_of_SC hA.1)
  Ei_cl := fun Z hZ hgZ => by
    have hωZ : ω < Z := omega0_lt_inE (Low.opow_eq_self_of_SC hZ)
    have hgj : yrG (yhJ E) < Z := by
      have hQ : yrQE E = yrQ (yhJ E) := yrQE_atom hA hjE
      exact yrG_of_Q hωZ (by rw [← hQ]; exact (le_max_right _ _).trans_lt hgZ)
    have hj := va_cl_code hE hBE hEU hlim hIH hZ hjE hgj
    rw [← va_at_E hA hjE, tf_gcG]
    exact TlCl.gam hZ.1 (TlCl.add (TlCl.add TlCl.om (TlCl.one hZ.1)) hj)
      ((lt_add_one _).trans_le le_self_add)
  V_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, hID2⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    obtain ⟨-, hD2T, -, -, hD2X⟩ := va_D2_facts hx hx1
    obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
    have hcl : YwClosed x (ywV 1 1 x) := ywV_closed hx hx1 zero_lt_one h1T h1Ω h1T h1Ω
    rw [vA_atom hA hjE, vI_high hjB]
    exact ⟨hqT, hqE, le_self_add.trans (gmq_gt hx hx1 hIT hI1).le, (hcl _ hIT hID2).trans hD2X⟩
  Vq := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hsT, hs1⟩ := gl_T_succ hx hx1 hIT hI1
    obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hIT hI1
    rw [vA_atom hA hjE, vI_high hjB]
    exact ⟨_, hsT, hs1, ((ev_isSuccLimit_of_inE hqE).add_one_lt (gmq_gt hx hx1 hIT hI1)).trans_le le_add_self,
      gmq_lt hx hx1 hsT hs1 (lt_add_one _)⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨hIT, hI1, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx
    obtain ⟨hqT, -, hq1, -, -⟩ := geq_facts hx hx1 hIT hI1
    rw [vA_atom hA hjE, vI_high hjB]
    exact ⟨hqT, hq1, va_eN_gq hx hx1 hIT hI1⟩
  V_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := va_at_o hjE
    obtain ⟨-, hgo⟩ := va_at_gate hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH
      (va_ltTat hE hBE hEU hlim hIH hA hjB hjE) hoE
    have hGo := va_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [vA_atom hA hjE, vI_high hjB, vA_atom hA hjE, vI_high hjB]
    exact hq
  W_pi := fun σ ρ hB hgσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ := hgσ.trans hB.2.2.1
    have hoE := va_at_o hjE
    obtain ⟨-, hgo⟩ := va_at_gate hA hjB hjE hB.1 hgσ
    obtain ⟨M, hoM, -, hEg, -, hR, hG, -⟩ := va_memV hE hBE hEU hlim hIH
      (va_ltTat hE hBE hEU hlim hIH hA hjB hjE) hoE
    have hGo := va_memG (omega0_lt_inE hB.1) hEg hgo hG hoM hgo
    obtain ⟨e1, e2⟩ := M.ex σ ρ _ hB hoM hGo
    rw [hR _ hoM ρ hB.2.1 hρ1 (hGo.trans hB.2.2.1)] at e1 e2
    rw [hR _ hoM σ hB.1 hσ1 hGo] at e2
    obtain ⟨d1, d2⟩ := zmD_pi hB
    obtain ⟨s1, s2⟩ := pi_add hB d1 e1
    rw [d2, e2] at s2
    obtain ⟨-, hI1ρ, -⟩ := va_at_I hE hBE hEU hlim hIH hA hjB hjE hB.2.1 hρ1 hgρ
    have h0 : (0 : Ordinal.{0}) < σ := hB.1.pos
    have hq := ywV_pi hB (mem_TB_of_lt hB h0) (h0.trans hσ1) s1 hI1ρ
    rw [ywV_zero, pi_lt hB h0, ywV_zero, s2] at hq
    rw [vA_atom hA hjE, vI_high hjB, vA_atom hA hjE, vI_high hjB]
    exact hq
  lt := fun x hx hx1 hgx c hc hg => va_ltTat hE hBE hEU hlim hIH hA hjB hjE x hx hx1 hgx c hc hg
  top := fun x hx hx1 hgx ν hν => by
    rw [vA_atom hA hjE, vI_high hjB] at hν
    exact va_top_at hE hBE hEU hlim hIH hA hjB hjE hx hx1 hgx ν hν

end Atom

/-- **A DIGIT SYSTEM READ BY `vR` AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < B₂`** (atoms included). -/
theorem vaGood_all2 : ∀ E, InE E → tfBG ≤ E → E < vaB2 → VaGood E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE hBE hEU
  rcases hBE.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact vaGood_BG
  by_cases hs : ∃ e, InE e ∧ tfBG ≤ e ∧ e < E ∧ eN e = E
  · obtain ⟨e, he, heB, heE, rfl⟩ := hs
    exact vaGood_succ he heB (heE.trans hEU) (IH e heE he heB (heE.trans hEU))
  · have hlim : ∀ e, InE e → e < E → eN e < E := by
      intro e he heE
      refine lt_of_le_of_ne (eN_le heE hE) fun h => ?_
      rcases lt_or_ge e tfBG with heB | heB
      · have h1 : eN e ≤ tfBG := eN_le heB (Low.opow_eq_self_of_SC tfBG_SC)
        rw [h] at h1
        exact absurd hlt (not_lt.2 h1)
      · exact hs ⟨e, he, heB, heE, h⟩
    have hIH : ∀ e, InE e → tfBG ≤ e → e < E → VaGood e := fun e he heB heE => IH e heE he heB (heE.trans hEU)
    rcases va_atom_cases2 hBE hEU with h | ⟨hA, hjB, hjE⟩ | hnA
    · exact absurd h hlt.ne'
    · exact vaGood_lim hE hlt hEU hlim hIH (vaTopAt hE hlt hEU hlim hIH hA hjB hjE)
    · exact vaGood_lim hE hlt hEU hlim hIH (vaTopNA hE hlt hEU hlim hIH hnA)

end Googology.Trans.PoR.InaccPsi.R2.Va
