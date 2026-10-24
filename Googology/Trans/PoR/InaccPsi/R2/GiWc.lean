import Googology.Trans.PoR.InaccPsi.R2.GiSqI

/-!
# THE CODE SYSTEM BELOW `ε_{Ω₁+1}^ω`: the codes `ε_{Ω₁+1}^k·d + r` (`1 ≤ k < ω`, `0 < d < ε_{Ω₁+1}`, `r < ε_{Ω₁+1}^k`)

Every code `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}^ω)` is `E^k·d + r` with `E = ε_{Ω₁+1}`, `k = log_E c` finite and `≥ 1`, a digit
`0 < d < E` (a code of `R2.GfSub`) and `r < E^k` (again such a code or a code below `E`).  The reading replaces `E` by
`ε_{x+1}` and reads the digits with `Ω₁ ↦ x`: `gwR c x = ε_{x+1}^k·d(x) + r(x)`; the gate is the largest gate of a digit
(`0` for a finite digit, as `Gi.giQ`), hereditarily.  Below `ε_{Ω₁+1}²` these are `Gi.giR` and `Gi.giG`.

* `gwB` (`ε_{Ω₁+1}^ω`), `gwR`, `gwG`, `gw_cnf` (the normal form), `gwR_cnf`, `gwG_cnf`, `gw_parts`, `gw_log_lt`;
* `gw_add` (**the gate of a sum**), `gw_code_gate` (**a code `c < ε_{Ω₁+1}^ω` over `Z`, all atoms above
  `ε_{Ω₁+1}^ω`, has its gate below `Z`**), `gwG_lt_Om1`.

No new axiom.  New definitions: `gwB`, `gwR`, `gwG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gw_one_lt : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW

theorem gw_ne_of_le {c : Ordinal.{0}} (h : gfE ≤ c) : c ≠ 0 := (lt_of_lt_of_le eW_E.pos h).ne'

/-- **The bound**: `ε_{Ω₁+1}^ω`. -/
noncomputable def gwB : Ordinal.{0} := gfE ^ ω

/-- **The reading** of `c = E^k·d + r` at `x`: `ε_{x+1}^k·d(x) + r(x)`. -/
noncomputable def gwR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c then eN x ^ log gfE c * rdc (c / gfE ^ log gfE c) x + gwR (c % gfE ^ log gfE c) x
  else rdc c x
termination_by c
decreasing_by exact mod_opow_log_lt_self gfE (gw_ne_of_le h)

/-- **The gate** of `c = E^k·d + r`. -/
noncomputable def gwG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c then max (giQ (c / gfE ^ log gfE c)) (gwG (c % gfE ^ log gfE c)) else gtc c
termination_by c
decreasing_by exact mod_opow_log_lt_self gfE (gw_ne_of_le h)

theorem gwR_low {c : Ordinal.{0}} (hc : c < gfE) (x : Ordinal.{0}) : gwR c x = rdc c x := by
  rw [gwR, dif_neg (not_le.2 hc)]

theorem gwG_low {c : Ordinal.{0}} (hc : c < gfE) : gwG c = gtc c := by
  rw [gwG, dif_neg (not_le.2 hc)]

theorem gwR_dec {c : Ordinal.{0}} (hc : gfE ≤ c) (x : Ordinal.{0}) :
    gwR c x = eN x ^ log gfE c * rdc (c / gfE ^ log gfE c) x + gwR (c % gfE ^ log gfE c) x := by
  rw [gwR, dif_pos hc]

theorem gwG_dec {c : Ordinal.{0}} (hc : gfE ≤ c) :
    gwG c = max (giQ (c / gfE ^ log gfE c)) (gwG (c % gfE ^ log gfE c)) := by
  rw [gwG, dif_pos hc]

/-- **The normal form** `E^k·d + r`. -/
theorem gw_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gfE) (hr : r < gfE ^ k) :
    log gfE (gfE ^ k * d + r) = k ∧ (gfE ^ k * d + r) / gfE ^ k = d ∧ (gfE ^ k * d + r) % gfE ^ k = r ∧
      gfE ≤ gfE ^ k * d + r := by
  have hp : gfE ^ k ≠ 0 := opow_ne_zero _ gfE_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [log_opow_mul_add gw_one_lt hd0 hr, log_eq_zero hdE, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  · calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk)
      _ = gfE ^ k * 1 := (mul_one _).symm
      _ ≤ gfE ^ k * d := mul_le_mul_left' (one_le_iff_ne_zero.2 hd0) _
      _ ≤ _ := le_self_add

theorem gwR_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gfE) (hr : r < gfE ^ k)
    (x : Ordinal.{0}) : gwR (gfE ^ k * d + r) x = eN x ^ k * rdc d x + gwR r x := by
  obtain ⟨h1, h2, h3, h4⟩ := gw_cnf hk hd0 hdE hr
  rw [gwR_dec h4, h1, h2, h3]

theorem gwG_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gfE) (hr : r < gfE ^ k) :
    gwG (gfE ^ k * d + r) = max (giQ d) (gwG r) := by
  obtain ⟨h1, h2, h3, h4⟩ := gw_cnf hk hd0 hdE hr
  rw [gwG_dec h4, h1, h2, h3]

/-- **The parts of a code `c ≥ ε_{Ω₁+1}`.** -/
theorem gw_parts {c : Ordinal.{0}} (hc : gfE ≤ c) :
    log gfE c ≠ 0 ∧ c / gfE ^ log gfE c ≠ 0 ∧ c / gfE ^ log gfE c < gfE ∧
      c % gfE ^ log gfE c < gfE ^ log gfE c ∧ gfE ^ log gfE c * (c / gfE ^ log gfE c) + c % gfE ^ log gfE c = c := by
  have hc0 := gw_ne_of_le hc
  refine ⟨?_, (div_opow_log_pos gfE hc0).ne', div_opow_log_lt c gw_one_lt,
    Ordinal.mod_lt c (opow_ne_zero _ gfE_ne), Ordinal.div_add_mod c _⟩
  have := le_log_of_opow_le gw_one_lt (show gfE ^ (1 : Ordinal.{0}) ≤ c by rw [opow_one]; exact hc)
  exact (zero_lt_one.trans_le this).ne'

theorem gw_log_lt {c : Ordinal.{0}} (hc : c < gwB) (hEc : gfE ≤ c) : log gfE c < ω :=
  (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hEc)).1 hc

theorem gw_pow_lt {k : Ordinal.{0}} (hk : k < ω) : gfE ^ k < gwB :=
  (opow_lt_opow_iff_right gw_one_lt).2 hk

theorem gwB_eq : gwB = ω ^ ghE := by
  rw [gwB, ghE, opow_mul, show ω ^ gfE = gfE from eW_E]

theorem gw_pow_eq (k : Ordinal.{0}) : gfE ^ k = ω ^ (gfE * k) := by
  rw [opow_mul, show ω ^ gfE = gfE from eW_E]

theorem gw_pow_indec {k : Ordinal.{0}} (hk : k ≠ 0) : ∀ u v, u < gfE ^ k → v < gfE ^ k → u + v < gfE ^ k := by
  intro u v hu hv
  rw [gw_pow_eq] at hu hv ⊢
  exact isPrincipal_add_omega0_opow _ hu hv

/-! ## The gate -/

theorem gwG_zero : gwG 0 = 0 := by rw [gwG_low eW_E.pos, gtc_zero]

theorem gwG_lt_Om1 : ∀ c, c < gwB → gwG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE]; exact gtc_lt_Om1 c hcE
  obtain ⟨-, -, hdE, hr, -⟩ := gw_parts hcE
  rw [gwG_dec hcE]
  have hrc : c % gfE ^ log gfE c < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  exact max_lt ((giQ_le _).trans_lt (gtc_lt_Om1 _ hdE)) (IH _ hrc (hrc.trans hc))

/-- **The gate of a sum** of codes below `ε_{Ω₁+1}^ω`, below every `Z > ω` closed under `+`. -/
theorem gw_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < gwB → gwG x < Z → gwG y < Z → gwG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  rcases lt_or_ge x gfE with hxE | hxE
  · rcases lt_or_ge y gfE with hyE | hyE
    · rw [gwG_low hxE] at hgx
      rw [gwG_low hyE] at hgy
      rw [gwG_low (eW_indec.add_lt hxE hyE)]
      exact gtc_add hZ x y hxE hyE hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gfE) (by rw [eW_E]; exact hxE) (by rw [eW_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hk, hd0, hdE, hr, hdec⟩ := gw_parts hxE
  set k := log gfE x with hkdef
  set d := x / gfE ^ k with hddef
  set r := x % gfE ^ k with hrdef
  have hrx : r < x := mod_opow_log_lt_self gfE (gw_ne_of_le hxE)
  rw [gwG_dec hxE] at hgx
  have hgd : gtc d < Z := gtc_lt_of_giQ hωZ ((le_max_left _ _).trans_lt hgx) hdE
  have hgr : gwG r < Z := (le_max_right _ _).trans_lt hgx
  rcases lt_or_ge y (gfE ^ k) with hyk | hyk
  · -- `x + y = E^k·d + (r + y)`
    have hry : r + y < gfE ^ k := gw_pow_indec hk _ _ hr hyk
    have e : x + y = gfE ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    rw [e, gwG_cnf hk hd0 hdE hry]
    have hrB : r + y < gwB := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    exact max_lt ((le_max_left _ _).trans_lt hgx) (IH r hrx y hrB hgr hgy)
  rcases lt_or_ge y (gfE ^ (k + 1)) with hyk1 | hyk1
  · -- `E^k ≤ y < E^{k+1}`: `y = E^k·d' + r'`
    have hEk : gfE ≤ gfE ^ k := by
      calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk)
    have hyE : gfE ≤ y := hEk.trans hyk
    have hky : log gfE y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le gw_one_lt hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hyE)).1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec'⟩ := gw_parts hyE
    rw [hky] at hd0' hdE' hr' hdec'
    rw [gwG_dec hyE, hky] at hgy
    set d' := y / gfE ^ k with hd'def
    set r' := y % gfE ^ k with hr'def
    have hgd' : gtc d' < Z := gtc_lt_of_giQ hωZ ((le_max_left _ _).trans_lt hgy) hdE'
    have hrω : r < ω ^ (gfE * k) := by rw [← gw_pow_eq]; exact hr
    have hab : r + gfE ^ k * d' = gfE ^ k * d' := by
      rw [gw_pow_eq]
      exact add_of_omega0_opow_le hrω (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = gfE ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < gfE := eW_indec.add_lt hdE hdE'
    rw [e, gwG_cnf hk (by
      intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr']
    exact max_lt ((giQ_le _).trans_lt (gtc_add hZ d d' hdE hdE' hgd hgd')) ((le_max_right _ _).trans_lt hgy)
  · -- `y ≥ E^{k+1} > x`
    have hxk : x < gfE ^ (k + 1) := by
      rw [hkdef]; exact (lt_opow_iff_log_lt gw_one_lt (gw_ne_of_le hxE)).2 (lt_add_one _)
    have e : x + y = y := add_of_omega0_opow_le (b := gfE * (k + 1)) (by rw [← gw_pow_eq]; exact hxk)
      (by rw [← gw_pow_eq]; exact hyk1)
    rw [e]; exact hgy

/-- **The gate of a code below `ε_{Ω₁+1}^ω`**: a code over `Z` (atoms above `ε_{Ω₁+1}^ω`) has its gate below `Z`. -/
theorem gw_code_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, gwB < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < gwB → gwG c < Z := by
  have hEB : gfE < gwB := by
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ < gwB := gw_pow_lt one_lt_omega0
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => hEB.trans (hAt s hs)
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gfE → gwG x < Z := fun x hx h => by
    rw [gwG_low h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    exact gw_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h hge ⊢
      have hyB : y < gwB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
      have hEy : gfE ≤ y := by
        rw [← show ω ^ gfE = gfE from eW_E] at hge
        exact (opow_le_opow_iff_right one_lt_omega0).1 hge
      have hyW : y < ghE := by
        rw [gwB_eq] at h; exact (opow_lt_opow_iff_right one_lt_omega0).1 h
      -- `y = E·m + y'`, `ω^y = E^m·ω^{y'}`
      obtain ⟨m, hm⟩ := gh_div_nat hyW
      have hm0 : (m : Ordinal.{0}) ≠ 0 := by
        rw [← hm]; exact (Ordinal.div_pos gfE_ne).2 hEy |>.ne'
      set y' := y % gfE with hy'
      have hy'E : y' < gfE := gh_mod_lt y
      have ey : y = gfE * (m : Ordinal.{0}) + y' := by rw [← hm]; exact (Ordinal.div_add_mod y gfE).symm
      have ew : ω ^ y = gfE ^ (m : Ordinal.{0}) * ω ^ y' + 0 := by
        rw [add_zero, ey, opow_add, gw_pow_eq]
      have hw0 : ω ^ y' ≠ 0 := opow_ne_zero _ omega0_ne_zero
      have hwE : ω ^ y' < gfE := by
        rw [← show ω ^ gfE = gfE from eW_E]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hy'E
      have hgy := ihy hyB
      have ey1 : y = gfE ^ (1 : Ordinal.{0}) * (m : Ordinal.{0}) + y' := by rw [opow_one]; exact ey
      have hmE : (m : Ordinal.{0}) < gfE := (natCast_lt_omega0 m).trans (omega_lt_Om1.trans Om1_lt_eW)
      rw [ey1, gwG_cnf one_ne_zero hm0 hmE (by rw [opow_one]; exact hy'E), gwG_low hy'E] at hgy
      rw [ew, gwG_cnf hm0 hw0 hwE (opow_pos _ eW_E.pos), gwG_zero]
      exact max_lt ((giQ_le _).trans_lt (gtc_opow hZw hy'E ((le_max_right _ _).trans_lt hgy))) hZ0
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have hBe : gwB < eN gfE := by
        rw [gwB_eq]
        have h2 : ghE < eN gfE := by
          rw [ghE_eq]
          have h3 : gfE + 1 < eN gfE :=
            (inE_indec (eN_E gfE)).add_lt (lt_eN gfE) (one_lt_omega0.trans (omega0_lt_inE (eN_E gfE)))
          have := (opow_lt_opow_iff_right one_lt_omega0).2 h3
          rwa [show ω ^ eN gfE = eN gfE from eN_E gfE] at this
        have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
        rwa [show ω ^ eN gfE = eN gfE from eN_E gfE] at this
      have heq : veblen x y = gfE := by
        rcases hge.lt_or_eq with hlt | heq
        · exact absurd ((eN_le hlt hE).trans_lt h) (not_lt.2 hBe.le)
        · exact heq.symm
      have e : gfE = gfE ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
      rw [heq, e, gwG_cnf one_ne_zero one_ne_zero gw_one_lt (opow_pos _ eW_E.pos), giQ_one, gwG_zero, max_self]
      exact hZ0

end Googology.Trans.PoR.InaccPsi.R2.Gi
