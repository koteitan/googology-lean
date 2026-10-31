import Googology.Trans.PoR.InaccPsi.R2.WfCarry
import Googology.Trans.PoR.InaccPsi.R2.WcSupLo
import Googology.Trans.PoR.InaccPsi.R2.SkSXPi

/-!
# The witness window with the restricted exponent clause

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`a = υ_λ = L(k)`, `u = υ_{λ+1}`, `g = ω^{ω^{u+1}}`, `μ` a Range restart with code `G₂+1` below `L(ω)` and below
`υ_λ`, `u' = υ_{μ+1}`, `g' = ω^{ω^{u'+1}}`, `X = ω^{ω^{u'+1}+1}`, `m(z) = cdOff(cdExp z)`, `π = π_{υ_μ,υ_λ}`.

* `wfPi_lt_next` (**`π_{σ,τ}` maps `Tᵗ[σ] ∩ Ω₁` below the next `υ`-point after `σ`**, from `pi_bijOn`,
  `T_inter_Om1`), `wfPiLo` (**the exponent clause `WcPiLo` restricted to `m z ∈ T^{υ_λ}[υ_μ]` is a THEOREM**:
  `π(m z) < u' < ω^{u'+1}`);
* `wfSide_false` (**REFUTATION**: the hypothesis `hside` of `Wc.wcQ_carry` and `Wc.wcSupLo` quantifies over every
  block map `Q`; it fails as soon as `Os` has an element other than `g`.  So `Wc.wcSupLo` is vacuous except at
  `Os ⊆ {g}`);
* `wfX_lt` (`X < E` for an `ε`-number `E > u'`);
* `wfOffMap` (**the map data at the witness window with the restricted exponent clause, for every `Os`**:
  `μ + X ≤ λ`, `ω² ∣ X`, `υ_{μ+X} ≤ r(μ)` (from `WcRead0`), an `Sl.SlOff` map `f` on `Os` with bound `X`,
  `f g = g'`, `π(m z) ≤ m(f z)` at every low offset with `m z ∈ T^{υ_λ}[υ_μ]`, EQ at the witness
  `img(Ew) = r(μ+g')`, and the low carry `img(ub(z+ω+1) + lo(m z)) ≤ r(μ+f z)` at those offsets).  Hypotheses only
  `Range(μ)`, its code, `υ_μ < L(ω)`, `WcRead0`, `υ_μ < υ_λ = L(k)`, `υ_λ < ν_C`; no `WcPiLo`, no `hside`, no `hCw`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`π_{σ,τ}(x) < m`** for `x ∈ Tᵗ[σ] ∩ Ω₁` and `m` the next `υ`-point after `σ`. -/
theorem wfPi_lt_next {σ τ m x : Ordinal.{0}} (hB : Bases σ τ) (hn : IsNext σ m) (hx : x ∈ TB τ σ)
    (hx1 : x < Om1) : pi σ τ x < m := by
  obtain ⟨m', -, -, hmin, hmT⟩ := T_inter_Om1 hB.1 (hB.2.2.1.trans hB.2.2.2)
  have hy1 := down_lt_Om1 hB hx hx1
  exact ((hmT _ hy1).1 ((pi_bijOn hB).1.mapsTo hx)).trans_le (hmin m hn.1 hn.2.1.2)

/-- **The restricted `WcPiLo` is a theorem**: `c ∈ T^{υ_λ}[υ_μ] ∩ Ω₁ ⇒ π_{υ_μ,υ_λ}(c) < ω^{υ_{μ+1}+1}`. -/
theorem wfPiLo {l μ c : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) (hc : c ∈ TB (upsilon l) (upsilon μ))
    (hc1 : c < Om1) : pi (upsilon μ) (upsilon l) c < ω ^ (upsilon (μ + 1) + 1) := by
  have h := wfPi_lt_next hB (upsilon_isNext μ) hc hc1
  rw [Order.succ_eq_add_one] at h
  exact h.trans_le ((right_le_opow _ one_lt_omega0).trans (opow_le_opow_right omega0_pos le_self_add))

/-- **REFUTATION of the side hypothesis of `Wc.wcQ_carry` / `Wc.wcSupLo`**: it asks the bounds for EVERY block map
`Q`; the constant map `Q = υ_{μ+2}` breaks `vyMap Q z < υ_{μ+2}` at any `z ∈ Os`, `z ≠ g`. -/
theorem wfSide_false {μ g : Ordinal.{0}} {Os : Finset Ordinal.{0}} (hz : ∃ z ∈ Os, z ≠ g) :
    ¬ ∀ Q : Ordinal.{0} → Ordinal.{0}, ∀ z ∈ Os, z ≠ g →
      ω ≤ Vy.vyMap Q z ∧ Vy.vyMap Q z < upsilon (μ + 2) ∧ upsilon (μ + Vy.vyMap Q z + ω + 1) < nuC := by
  intro h
  obtain ⟨z, hz, hzg⟩ := hz
  have h1 := (h (fun _ => upsilon (μ + 2)) z hz hzg).2.1
  have h2 : upsilon (μ + 2) ≤ Vy.vyMap (fun _ => upsilon (μ + 2)) z :=
    (Ordinal.le_mul_right _ Vy.vy_p).trans le_self_add
  exact absurd h1 (not_lt.2 h2)

/-- An `ε`-number is a successor limit. -/
theorem wf_inE_lim {E : Ordinal.{0}} (hE : InE E) (h0 : 0 < E) : IsSuccLimit E := by
  have : IsSuccLimit (ω ^ E) := isSuccLimit_opow_left isSuccLimit_omega0 h0.ne'
  unfold InE at hE; rwa [hE] at this

/-- **`X = ω^{ω^{u+1}+1} < E`** for an `ε`-number `E > u`. -/
theorem wfX_lt {E u : Ordinal.{0}} (hE : InE E) (hu : u < E) : Wc.wcX u < E := by
  have hl := wf_inE_lim hE (lt_of_le_of_lt zero_le hu)
  have hE' : ω ^ E = E := hE
  have h1 : u + 1 < E := hl.add_one_lt hu
  have h2 : ω ^ (u + 1) < E := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 h1; rwa [hE'] at this
  have h3 : ω ^ (u + 1) + 1 < E := hl.add_one_lt h2
  have h4 := (opow_lt_opow_iff_right one_lt_omega0).2 h3
  rw [hE'] at h4
  exact h4

/-- `ω < X`. -/
theorem wf_om_lt_X (u : Ordinal.{0}) : ω < Wc.wcX u := by
  unfold Wc.wcX
  have h1 : (1 : Ordinal.{0}) < ω ^ (u + 1) + 1 := by
    have : (0 : Ordinal.{0}) < ω ^ (u + 1) := opow_pos _ omega0_pos
    exact (Order.one_le_iff_pos.2 this).trans_lt (lt_add_one _)
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h1
  rwa [opow_one] at this

/-- `ω² < X`. -/
theorem wf_om2_lt_X (u : Ordinal.{0}) : ω ^ 2 < Wc.wcX u := by
  unfold Wc.wcX
  rw [← Ordinal.opow_natCast]
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
  have h2 : ((2 : ℕ) : Ordinal.{0}) < ω := natCast_lt_omega0 2
  exact h2.trans_le ((left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u))).trans le_self_add)

/-- `y + ω + 1 < X` for `y < X`. -/
theorem wf_add_lt_X {u y : Ordinal.{0}} (hy : y < Wc.wcX u) : y + ω + 1 < Wc.wcX u := by
  have hP : IsPrincipal (· + ·) (Wc.wcX u) := by unfold Wc.wcX; exact isPrincipal_add_omega0_opow _
  have hω := wf_om_lt_X u
  exact hP (hP hy hω) (one_lt_omega0.trans hω)

/-- **The map data at the witness window, restricted exponent clause.** -/
theorem wfOffMap (k : ℕ) {l μ : Ordinal.{0}} (hlk : Nc.ncL S (k : Ordinal.{0}) = upsilon l)
    (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω)
    (hr : Wc.WcRead0 S μ) (hμl : upsilon μ < upsilon l) (hlν : upsilon l < nuC) (Os : Finset Ordinal.{0}) :
    ∃ f : Ordinal.{0} → Ordinal.{0}, ∃ B, μ + B ≤ l ∧ ω ^ 2 ∣ B ∧ upsilon (μ + B) ≤ cdR S μ ∧
      Sl.SlOff f Os B ∧
      (ω ^ ω ^ (upsilon (l + 1) + 1) ∈ Os → f (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
      (∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → cdOff (cdExp z) < upsilon (l + 1) →
        cdOff (cdExp z) ∈ TB (upsilon l) (upsilon μ) →
        pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z))) ∧
      Vr.vrImg l μ f (Vr.vrEw (ω ^ ω ^ (upsilon (l + 1) + 1))) = cdR S (μ + ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
      (∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
        cdOff (cdExp z) ∈ TB (upsilon l) (upsilon μ) → cdOff (cdExp z) < Om1 →
        Vr.vrImg l μ f (.add (.ub (z + ω + 1) .base) (.lo (cdOff (cdExp z)))) ≤ cdR S (μ + f z)) := by
  classical
  have hm := upsilon_normal.strictMono
  -- the facts on `λ`
  have hll : upsilon l = l := hm.injective (by rw [← hlk]; exact Te.teUps_L k)
  have hμl' : μ < l := hm.lt_iff_lt.1 hμl
  have hl0 : 0 < l := lt_of_le_of_lt zero_le hμl'
  have hlE' : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hlE : InE l := by rw [← hll]; exact hlE'
  have hlim := wf_inE_lim hlE hl0
  have hl1 : upsilon l < Om1 := hlν.trans_le nuC_le_Om1
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon hμ0)
  have hB : Bases (upsilon μ) (upsilon l) := ⟨hμE, hlE', hμl, hl1⟩
  have hμ2 : μ + 2 < l := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc]
    exact hlim.add_one_lt (hlim.add_one_lt hμl')
  have hu2E : InE (upsilon (μ + 2)) :=
    upsPt_inE (upsPt_upsilon (lt_of_lt_of_le hμ0 le_self_add))
  have hu12 : upsilon (μ + 1) < upsilon (μ + 2) := hm (by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc]; exact lt_add_one _)
  set X := Wc.wcX (upsilon (μ + 1)) with hXdef
  have hXu2 : X < upsilon (μ + 2) := wfX_lt hu2E hu12
  have hu2l : upsilon (μ + 2) < l := by rw [← hll]; exact hm hμ2
  have hXl : X < l := hXu2.trans hu2l
  have hμX : μ + X < l := (inE_indec hlE).add_lt hμl' hXl
  have hu1 : upsilon (μ + 1) < Om1 := hu12.trans (hu2l.trans (hll ▸ hl1))
  have hn : upsilon (μ + 2) < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq]
    refine hu2l.trans ?_
    have := Te.teL_lt_omega (S := S) k
    rw [hlk, hll] at this
    exact this.trans (Qq.qqL_lt_succ S)
  have hinner : ∀ y, y < X → upsilon (μ + y + ω + 1) < nuC := by
    intro y hy
    have h1 : μ + y + ω + 1 < l := by
      rw [add_assoc, add_assoc, ← add_assoc y]
      exact lt_of_lt_of_le ((add_lt_add_iff_left μ).2 (wf_add_lt_X hy)) hμX.le
    have := hm h1
    rw [hll] at this
    exact this.trans (hll ▸ hlν)
  -- the block map
  set E := upsilon (l + 1) + 1 with hEdef
  have hE : (1 : Ordinal.{0}) ≤ E := le_add_self
  set g := ω ^ ω ^ E with hgdef
  set Os2 := insert g ((Os.image (fun z => ω ^ 2 * (z / ω ^ 2))).filter (fun z => 0 < z)) with hOs2
  have hOs2p : ∀ z ∈ Os2, 0 < z ∧ ω ^ 2 ∣ z := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨opow_pos _ omega0_pos, ⟨_, (Vu.vuPow_block hE).symm⟩⟩
    · obtain ⟨hz, hz0⟩ := Finset.mem_filter.1 hz
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
      exact ⟨hz0, dvd_mul_right _ _⟩
  set P : Ordinal.{0} → Ordinal.{0} := fun c =>
    if c ∈ TB (upsilon l) (upsilon μ) ∧ c < Om1 then pi (upsilon μ) (upsilon l) c else 0 with hPdef
  have hP : ∀ z ∈ Os2, z ≠ g → P (cdOff (cdExp z)) < ω ^ (upsilon (μ + 1) + 1) := by
    intro z _ _
    simp only [hPdef]
    split_ifs with h
    · exact wfPiLo hB h.1 h.2
    · exact opow_pos _ omega0_pos
  obtain ⟨Q, hQ0, hQg, hfg, hoff2, hexp⟩ :=
    Wc.wcQ_wit_lo (u' := upsilon (μ + 1)) P hE hOs2p (Finset.mem_insert_self _ _) hP
  set f := Vy.vyMap Q with hfdef
  have hp := Vy.vy_p
  -- the blocks of `Os` lie in `Os2`
  have hblk : ∀ x ∈ insert 0 Os, ω ^ 2 * (x / ω ^ 2) ∈ insert 0 Os2 := by
    intro x hx
    rcases eq_or_ne (ω ^ 2 * (x / ω ^ 2)) 0 with h0 | h0
    · rw [h0]; exact Finset.mem_insert_self _ _
    · have hxO : x ∈ Os := by
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact absurd (by rw [Ordinal.zero_div, mul_zero]) h0
        · exact hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨x, hxO, rfl⟩, pos_iff_ne_zero.2 h0⟩))
  have hQmono : ∀ x ∈ insert 0 Os, ∀ y ∈ insert 0 Os, x / ω ^ 2 < y / ω ^ 2 →
      Q (x / ω ^ 2) < Q (y / ω ^ 2) := by
    intro x hx y hy hxy
    have h1 : ω ^ 2 * (x / ω ^ 2) < ω ^ 2 * (y / ω ^ 2) := (mul_lt_mul_iff_right₀ hp).2 hxy
    have h2 : Vy.vyMap Q (ω ^ 2 * (x / ω ^ 2)) < Vy.vyMap Q (ω ^ 2 * (y / ω ^ 2)) :=
      hoff2.mono (Finset.mem_coe.2 (hblk x hx)) (Finset.mem_coe.2 (hblk y hy)) h1
    rw [Vy.vyMap_block, Vy.vyMap_block] at h2
    exact (mul_lt_mul_iff_right₀ hp).1 h2
  have hbd : ∀ d ∈ Os, f d < X := by
    intro d hd
    have hPX : IsPrincipal (· + ·) X := by rw [hXdef]; unfold Wc.wcX; exact isPrincipal_add_omega0_opow _
    have h1 : ω ^ 2 * Q (d / ω ^ 2) < X := by
      have hb := hblk d (Finset.mem_insert_of_mem hd)
      rcases Finset.mem_insert.1 hb with h0 | hb
      · have hq : Q (d / ω ^ 2) = 0 := by
          have hd0 : d / ω ^ 2 = 0 := by
            rcases (mul_eq_zero.1 h0) with h | h
            · exact absurd h hp.ne'
            · exact h
          rw [hd0, hQ0]
        rw [hq, mul_zero]; exact lt_of_le_of_lt zero_le (wf_om_lt_X _)
      · have : Vy.vyMap Q (ω ^ 2 * (d / ω ^ 2)) < X := hoff2.bd _ hb
        rwa [Vy.vyMap_block] at this
    have h2 : d % ω ^ 2 < X := (Ordinal.mod_lt d hp.ne').trans (wf_om2_lt_X _)
    exact hPX h1 h2
  have hoff : Sl.SlOff f Os X := Vy.vyMap_slOff hQ0 hQmono hbd
  -- a positive `ω²`-divisible offset of `Os` lies in `Os2`
  have hin2 : ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → z ∈ Os2 := by
    intro z hz hz0 hzd
    have hze : ω ^ 2 * (z / ω ^ 2) = z := by
      obtain ⟨q, rfl⟩ := hzd; rw [Ordinal.mul_div_cancel _ hp.ne']
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨z, hz, hze⟩, hz0⟩)
  -- `m g ≥ υ_{λ+1}`
  have hmg : ¬ cdOff (cdExp g) < upsilon (l + 1) := by
    rw [hgdef, R2Skel.SkSX.skSX_cdExp_opow]
    have hω1 : ω ≤ ω ^ E := by
      have := opow_le_opow_right omega0_pos hE; rwa [opow_one] at this
    unfold cdOff; rw [if_neg (not_lt.2 hω1)]
    exact not_lt.2 ((le_self_add.trans (right_le_opow _ one_lt_omega0)))
  -- the low bound of `P`
  have hPm : ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z → z ≠ g → cdOff (cdExp z) ∈ TB (upsilon l) (upsilon μ) →
      cdOff (cdExp z) < Om1 → pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) ≤ cdOff (cdExp (f z)) := by
    intro z hz hz0 hzd hzg hT h1
    have := hexp z (hin2 z hz hz0 hzd) hzg
    simp only [hPdef, if_pos (And.intro hT h1)] at this
    exact this
  -- the side conditions at the produced map
  have hside : ∀ z ∈ Os, 0 < z → ω ^ 2 ∣ z →
      ω ≤ f z ∧ f z < upsilon (μ + 2) ∧ upsilon (μ + f z + ω + 1) < nuC := by
    intro z hz hz0 hzd
    have hfz : f 0 < f z := hoff.mono (Finset.mem_coe.2 (Finset.mem_insert_self 0 Os))
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem hz)) hz0
    rw [hoff.zero] at hfz
    have hd : ω ^ 2 ∣ f z := by
      obtain ⟨q, rfl⟩ := hzd; exact hoff.dvd q
    have hω2 : ω ^ 2 ≤ f z := le_of_dvd hfz.ne' hd
    have hωω : ω ≤ ω ^ 2 := by rw [pow_two]; exact Ordinal.le_mul_left _ omega0_pos
    exact ⟨hωω.trans hω2, (hoff.bd z hz).trans hXu2, hinner _ (hoff.bd z hz)⟩
  have hg' : ω ^ ω ^ (upsilon (μ + 1) + 1) < X := by
    have := Wc.wcX_gt (upsilon (μ + 1)); exact lt_of_le_of_lt le_self_add this
  refine ⟨f, X, hμX.le, Wc.wcX_dvd _, (Wc.wcSup hR hc hω hr).2.2, hoff, fun _ => hfg, ?_, ?_, ?_⟩
  · intro z hz hz0 hzd hzl hT
    by_cases hzg : z = g
    · rw [hzg] at hzl; exact absurd hzl hmg
    · exact hPm z hz hz0 hzd hzg hT (hzl.trans (by
        have := next_lt_Om1 (upsilon_isNext l) (Or.inr (upsPt_upsilon hl0)) hl1
        rwa [Order.succ_eq_add_one] at this))
  · exact (Vy.vyEQ_wit (S := S) hB hoff hQg hR.1 hu1 hn (hinner _ hg')).2
  · intro z hz hz0 hzd hzg hT h1
    obtain ⟨hω', hfu, hC⟩ := hside z hz hz0 hzd
    exact (Vy.vyEQ_lo (S := S) hoff hzd hR.1 hn hω' hfu hC).2 (hPm z hz hz0 hzd hzg hT h1)

end Googology.Trans.PoR.InaccPsi.R2.Wf
