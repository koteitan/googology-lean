import Googology.Trans.PoR.InaccPsi.R2.HnPw

/-!
# HoLv: THE BAND LEVEL DATUM `Ω₁·Ω₁·v + Ω₁·M` FOR EVERY PREFIX `1 ≤ v < Ω₁`, `M < Ω₁`

Generalizes `Hn.hnMLv` (prefix `Ω₁·Ω₁`, i.e. `v = 1`) to the prefix `Ω₁·Ω₁·v` for every `1 ≤ v < Ω₁`: the level
`Ω₁·Ω₁·v + Ω₁·M` is read `x·x·v + x·M` above the gate `max (hlGt v) (hlGt M)` and `x·x` at or below it.

* `ho_vt_opow` (`ϑʳ(g) = ω^{r+g}` for `1 ≤ g ≤ r + r`; the proof of `Exact.vt_opow` with the bound `r + r`),
  `ho_pi_sqopow` (**EXACT for `ω^{ρ+ρ+h}`**, `h < σ`), `ho_pi_sqmul` (**EXACT for `ρ·ρ·γ`**, `γ < σ`);
* `ho_sqmul_mem` (`Ω₁·Ω₁·v` in every hull `C(a, b)` with `v < ε₀` or `v < b`);
* `ho_cl_sq`, `ho_cl_band` (**THE TWO GATES FROM A CODE**: a code over `Z` in `[Ω₁²·v + Ω₁·M, Ω₁²·(v+1))` has
  `v < Z` (`Hn.hn_cl_digit`, `k = 2`) and `M < Z` (`Hn.hn_band_gate_k`, `k = 1`));
* `hoLv v M` (**THE BAND LEVEL DATUM**), `hoLv_L`, `hoLv_l`, `hoLv_g`;
* `HoGood v Λ` (a level below the next prefix `Ω₁²·(v+1)`, read below `x·x·(v+1)`), `hoGood_of`;
* `hoZo` (the outer low field `φ(x·x·x, Γ_{x+1}+1)`, one for every prefix).

No new axiom.  New definitions: `hoRd`, `hoLv`, `HoGood`, `hoZo`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Lemma EXACT for `ρ·ρ·γ` -/

/-- **`ϑʳ(g) = ω^{r+g}`** for an `ε`-number `r < Ω₁` and `1 ≤ g ≤ r + r` (no `ε`-number in `(r, r+g]`). -/
theorem ho_vt_opow {r g : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (hg1 : 1 ≤ g) (hgr : g ≤ r + r) :
    vt r g = ω ^ (r + g) := by
  have he : 1 + (g - 1) = g := Ordinal.add_sub_cancel_of_le hg1
  have hα1 : g - 1 < Om1 :=
    lt_of_le_of_lt (sub_le_self g 1) (lt_of_le_of_lt hgr ((inE_indec gl_Om1_E).add_lt hr1 hr1))
  rw [← he, vt_wbar hr hr1 hα1, wbar_eq hr, add_assoc]
  intro β hrβ hβ hE
  have hI := inE_indec hE
  have : r + (r + r) < β := hI.add_lt hrβ (hI.add_lt hrβ hrβ)
  rw [add_assoc, he] at hβ
  exact absurd (hβ.trans (add_le_add le_rfl hgr)) (not_le.2 this)

/-- **`π_{σ,ρ}(ω^{ρ+ρ+h}) = ω^{σ+σ+h}`** for `h < σ` ([W07a] Lemma 4.2, Def 5.1 via `vt_wbar`, `pi_vt`). -/
theorem ho_pi_sqopow {s r h : Ordinal.{0}} (hB : Bases s r) (hhs : h < s) :
    ω ^ (r + r + h) ∈ TB r s ∧ pi s r (ω ^ (r + r + h)) = ω ^ (s + s + h) := by
  obtain ⟨hsE, hrE, hsr, hr1⟩ := hB
  have hB' : Bases s r := ⟨hsE, hrE, hsr, hr1⟩
  have hhr : h < r := hhs.trans hsr
  obtain ⟨hbT, hbP⟩ := pi_base hB'
  have hhT := mem_TB_of_lt hB' hhs
  obtain ⟨hgT, hgP⟩ := pi_add hB' hbT hhT
  rw [hbP, pi_lt hB' hhs] at hgP
  have hO : r + h < Om1 := (inE_indec gl_Om1_E).add_lt hr1 (hhr.trans hr1)
  have h1 : (1 : Ordinal.{0}) ≤ r + h := (one_le_iff_pos.2 hrE.pos).trans le_self_add
  have hv := ho_vt_opow hrE hr1 h1 (add_le_add le_rfl hhr.le)
  obtain ⟨hvT, hvP⟩ := vt_mem hrE hr1 hgT.1 hO
  rw [add_assoc r r h, add_assoc s s h]
  refine ⟨?_, ?_⟩
  · rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hgT.2⟩
  · rw [← hv, pi_vt hB' hgT hO, hgP, ho_vt_opow hsE (hsr.trans hr1)
      ((one_le_iff_pos.2 hsE.pos).trans le_self_add) (add_le_add le_rfl hhs.le)]

theorem ho_sq_opow {t : Ordinal.{0}} (ht : ω ^ t = t) (g : Ordinal.{0}) : t * t * ω ^ g = ω ^ (t + t + g) := by
  rw [opow_add, opow_add, ht]

/-- **Lemma EXACT for `ρ·ρ·γ`**: `π_{σ,ρ}(ρ·ρ·γ) = σ·σ·γ` for `γ < σ`. -/
theorem ho_pi_sqmul {s r : Ordinal.{0}} (hB : Bases s r) :
    ∀ γ, γ < s → r * r * γ ∈ TB r s ∧ pi s r (r * r * γ) = s * s * γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · simp only [mul_zero]
    exact ⟨mem_TB_of_lt hB (InE.pos hB.1), pi_lt hB (InE.pos hB.1)⟩
  set g := log ω γ with hg
  set q := γ / ω ^ g with hq
  set m := γ % ω ^ g with hm
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * q + m = γ := div_add_mod γ (ω ^ g)
  have hmlt : m < ω ^ g := mod_lt γ hω0
  have hgle : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  have hqω : q < ω := div_opow_log_lt γ one_lt_omega0
  obtain ⟨n, hn⟩ := lt_omega0.1 hqω
  have hgs : g < s := lt_of_le_of_lt (log_le_self ω γ) hγ
  have hrE : ω ^ r = r := hB.2.1
  have hsE : ω ^ s = s := hB.1
  obtain ⟨hPT, hPpi⟩ := ho_pi_sqopow hB hgs
  obtain ⟨hPnT, hPnpi⟩ := pi_mul_nat hB hPT hPpi n
  obtain ⟨hmT, hmpi⟩ := IH m (lt_of_lt_of_le hmlt hgle) (lt_of_lt_of_le hmlt (hgle.trans hγ.le))
  have hdecomp : ∀ t : Ordinal.{0}, ω ^ t = t → t * t * γ = ω ^ (t + t + g) * (n : Ordinal.{0}) + t * t * m := by
    intro t ht
    rw [← ho_sq_opow ht g]
    conv_lhs => rw [← hdm, hn, mul_add, ← mul_assoc]
  rw [hdecomp r hrE, hdecomp s hsE]
  obtain ⟨h1, h2⟩ := pi_add hB hPnT hmT
  exact ⟨h1, by rw [h2, hPnpi, hmpi]⟩

/-! ## Hull membership of `Ω₁·Ω₁·v` -/

theorem ho_OO_opow (e : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 * ω ^ e = veblen 0 (Om 1 + (Om 1 + e)) := by
  rw [mul_assoc, hk_om_opow, veblen_zero_apply, hk_om_opow]

theorem ho_gt_or {v b : Ordinal.{0}} (h : hlGt v < b) : v < ε₀ ∨ v < b := by
  unfold hlGt at h; split_ifs at h with h1
  · exact Or.inl h1
  · exact Or.inr h

/-- **`Ω₁·Ω₁·v` lies in every hull `C(a, b)`** with `v < ε₀` or `v < b`. -/
theorem ho_sqmul_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) :
    ∀ v : Ordinal.{0}, (v < ε₀ ∨ v < b) → (Om1 : Ordinal.{0}) * Om1 * v ∈ S.CSet a b := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases eq_or_ne v 0 with rfl | h0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨hdr, hrd⟩ := hk_split h0
  have he : log ω v ∈ S.CSet a b := by
    rcases hv with hv | hv
    · exact gc_cst_mem a b _ ((gc_log_lt h0 hv).trans hv)
    · exact CSet.of_lt ((log_le_self ω v).trans_lt hv)
  have hw : (Om1 : Ordinal.{0}) * Om1 * ω ^ log ω v ∈ S.CSet a b := by
    rw [ho_OO_opow]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) he))
  rw [← hdr, mul_add]
  exact CSet.add_mem hw (IH _ hrd (hv.imp hrd.trans hrd.trans))

theorem ho_mul_mem' (S : InaccSeq.{0}) (a b M : Ordinal.{0}) (h : hlGt M < b) :
    (Om1 : Ordinal.{0}) * M ∈ S.CSet a b := by
  rcases ho_gt_or h with h' | h'
  · exact hk_mul_mem S a b M h'
  · exact hl_mul_mem S a b M h'

/-! ## The two gates from a code -/

theorem ho_OO_eq : (Om1 : Ordinal.{0}) * Om1 = ω ^ (Om 1 * ((2 : ℕ) : Ordinal.{0})) := by
  rw [Nat.cast_ofNat, mul_two_eq, opow_add, hn_Om_E, ← Br.Om1_eq]

theorem ho_OOO_eq : (Om1 : Ordinal.{0}) * Om1 * Om1 = ω ^ (Om 1 * ((2 + 1 : ℕ) : Ordinal.{0})) := by
  rw [Nat.cast_add, mul_add, Nat.cast_one, mul_one, opow_add, ← ho_OO_eq, hn_Om_E, ← Br.Om1_eq]

theorem ho_O_eq : (Om1 : Ordinal.{0}) = ω ^ (Om 1 * ((1 : ℕ) : Ordinal.{0})) := by
  rw [Nat.cast_one, mul_one, hn_Om_E, ← Br.Om1_eq]

theorem ho_OO_pos : (0 : Ordinal.{0}) < Om1 * Om1 := mul_pos gv_Om1_pos gv_Om1_pos

/-- **The prefix gate**: a code over a strongly critical `Z ≤ Ω₁` in `[Ω₁²·v, Ω₁³)` has `v < Z`. -/
theorem ho_cl_sq {Z y v : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y)
    (hlo : Om1 * Om1 * v ≤ y) (hhi : y < Om1 * Om1 * Om1) : v < Z := by
  have h := hn_cl_digit hZ hZ1 2 (by norm_num) hy
  rw [← ho_OOO_eq, ← ho_OO_eq, Ordinal.mod_eq_of_lt hhi] at h
  exact ((Ordinal.le_div ho_OO_pos.ne').2 hlo).trans_lt h

/-- **The band gate**: a code over a strongly critical `Z ≤ Ω₁` in `[Ω₁²·v + Ω₁·M, Ω₁²·v + Ω₁²)` has `M < Z`. -/
theorem ho_cl_band {Z y v M : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y)
    (hlo : Om1 * Om1 * v + Om1 * M ≤ y) (hhi : y < Om1 * Om1 * v + Om1 * Om1) : M < Z := by
  have hP : Om1 * Om1 * v ≤ y := le_self_add.trans hlo
  obtain ⟨d, rfl⟩ := exists_add_of_le hP
  have hd : d < Om1 * Om1 := (add_lt_add_iff_left _).1 hhi
  have hMd : Om1 * M ≤ d := (add_le_add_iff_left _).1 hlo
  have hdec : d = Om1 * (d / Om1) + d % Om1 := (div_add_mod d Om1).symm
  have hq : d / Om1 < Om 1 := by
    rw [← Br.Om1_eq]; exact (Ordinal.div_lt gv_Om1_pos.ne').2 hd
  have hr : d % Om1 < ω ^ (Om 1 * ((1 : ℕ) : Ordinal.{0})) := by
    rw [← ho_O_eq]; exact Ordinal.mod_lt d gv_Om1_pos.ne'
  have hdv : ω ^ (Om 1 * ((1 + 1 : ℕ) : Ordinal.{0})) ∣ Om1 * Om1 * v := by
    rw [← ho_OO_eq]; exact dvd_mul_right _ _
  have hy' : GxCl Z {gcG 0} (Om1 * Om1 * v + ω ^ (Om 1 * ((1 : ℕ) : Ordinal.{0})) * (d / Om1) + d % Om1) := by
    rw [← ho_O_eq, add_assoc, ← hdec]; exact hy
  have h := hn_band_gate_k hZ hZ1 1 le_rfl hdv hq hr hy'
  exact ((Ordinal.le_div gv_Om1_pos.ne').2 hMd).trans_lt h

/-! ## The band level datum -/

open Classical in
/-- **The reading of the band level `Ω₁·Ω₁·v + Ω₁·M`**: `x·x·v + x·M` above the gate, `x·x` at or below it. -/
noncomputable def hoRd (v M x : Ordinal.{0}) : Ordinal.{0} :=
  if max (hlGt v) (hlGt M) < x then x * x * v + x * M else x * x

theorem hoRd_eq {v M x : Ordinal.{0}} (h : max (hlGt v) (hlGt M) < x) : hoRd v M x = x * x * v + x * M := by
  unfold hoRd; rw [if_pos h]

theorem ho_sqv_lt_G {v : Ordinal.{0}} (hv : v < Om1) (α : Ordinal.{0}) : (Om1 : Ordinal.{0}) * Om1 * v < gcG α :=
  InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hl_OO_lt_G α) (hv.trans (hg_Om1_lt_G α))

theorem ho_L_lt_G {v M : Ordinal.{0}} (hv : v < Om1) (hM : M < Om1) (α : Ordinal.{0}) :
    (Om1 : Ordinal.{0}) * Om1 * v + Om1 * M < gcG α :=
  (inE_indec (Low.opow_eq_self_of_SC (gcG_SC α))).add_lt (ho_sqv_lt_G hv α)
    (InE.mul_lt (Low.opow_eq_self_of_SC (gcG_SC α)) (hg_Om1_lt_G α) (hM.trans (hg_Om1_lt_G α)))

theorem ho_next_le {v : Ordinal.{0}} (hv : v < Om1) :
    (Om1 : Ordinal.{0}) * Om1 * v + Om1 * Om1 ≤ Om1 * Om1 * Om1 := by
  rw [← mul_add_one]; exact mul_le_mul_left' (Order.add_one_le_of_lt hv) _

theorem ho_xsq_le {x v : Ordinal.{0}} (hv1 : 1 ≤ v) : x * x ≤ x * x * v := le_mul_of_one_le_right' hv1

/-- **THE BAND LEVEL DATUM `Ω₁·Ω₁·v + Ω₁·M`, READ AS `x·x·v + x·M`** above the gate `max (hlGt v) (hlGt M)`. -/
noncomputable def hoLv (v M : Ordinal.{0}) (hv1 : 1 ≤ v) (hv : v < Om1) (hM : M < Om1) : HnLv where
  L := Om1 * Om1 * v + Om1 * M
  l := hoRd v M
  u := Om1 * v
  q := M
  g := max (hlGt v) (hlGt M)
  g_lt := max_lt ((hlGt_le v).trans_lt hv) ((hlGt_le M).trans_lt hM)
  q_lt := hM
  OL := ((le_mul_of_one_le_right' hg_one_lt_Om1.le).trans (ho_xsq_le hv1)).trans le_self_add
  L_G := ho_L_lt_G hv hM 0
  L_eq := by rw [← Br.Om1_eq, mul_assoc]
  g_cl := fun Z y hZ hZ1 hy hLy hy2 => by
    have hy2' : y < Om1 * Om1 * v + Om1 * Om1 := by rw [← Br.Om1_eq] at hy2; rw [mul_assoc]; exact hy2
    exact max_lt ((hlGt_le v).trans_lt (ho_cl_sq hZ hZ1 hy (le_self_add.trans hLy)
      (hy2'.trans_le (ho_next_le hv)))) ((hlGt_le M).trans_lt (ho_cl_band hZ hZ1 hy hLy hy2'))
  L_mem := fun S a b _ hb => CSet.add_mem (ho_sqmul_mem S a b v (ho_gt_or ((le_max_left _ _).trans_lt hb)))
    (ho_mul_mem' S a b M ((le_max_right _ _).trans_lt hb))
  l_ge := fun x => by
    unfold hoRd; split_ifs
    · exact ((hn_le_sq x).trans (ho_xsq_le hv1)).trans le_self_add
    · exact hn_le_sq x
  l_lt := fun x hx hx1 => by
    unfold hoRd; split_ifs with h
    · have hE := (lgG_facts hx hx1).2.2.2.1
      have hxl := (lgG_facts hx hx1).2.1
      exact (inE_indec hE).add_lt (InE.mul_lt hE (hl_sq_lt hx hx1)
        ((hl_gt_E hx ((le_max_left _ _).trans_lt h)).trans hxl))
        (InE.mul_lt hE hxl ((hl_gt_E hx ((le_max_right _ _).trans_lt h)).trans hxl))
    · exact hl_sq_lt hx hx1
  l_pi := fun σ ρ hB hg => by
    rw [hoRd_eq hg, hoRd_eq (hg.trans hB.2.2.1)]
    obtain ⟨a1, a2⟩ := ho_pi_sqmul hB v (hl_gt_E hB.1 ((le_max_left _ _).trans_lt hg))
    obtain ⟨b1, b2⟩ := pi_mul hB M (hl_gt_E hB.1 ((le_max_right _ _).trans_lt hg))
    obtain ⟨c1, c2⟩ := pi_add hB a1 b1
    exact ⟨c1, by rw [c2, a2, b2]⟩

section Lv

variable {v M : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (hM : M < Om1)

theorem hoLv_L : (hoLv v M hv1 hv hM).L = Om1 * Om1 * v + Om1 * M := rfl

theorem hoLv_l {x : Ordinal.{0}} (hx : (hoLv v M hv1 hv hM).g < x) : (hoLv v M hv1 hv hM).l x = x * x * v + x * M :=
  hoRd_eq hx

theorem hoLv_g : (hoLv v M hv1 hv hM).g = max (hlGt v) (hlGt M) := rfl

/-- **Above the gate of `hoLv v M` at an `ε`-number `x`: `v < x` and `M < x`.** -/
theorem hoLv_gt {x : Ordinal.{0}} (hx : InE x) (h : (hoLv v M hv1 hv hM).g < x) : v < x ∧ M < x :=
  ⟨hl_gt_E hx ((le_max_left _ _).trans_lt h), hl_gt_E hx ((le_max_right _ _).trans_lt h)⟩

end Lv

theorem hoLv_L0 {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) : (hoLv v 0 hv1 hv gv_Om1_pos).L = Om1 * Om1 * v := by
  rw [hoLv_L, mul_zero, add_zero]

theorem hoLv_l0 {v x : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (hx : (hoLv v 0 hv1 hv gv_Om1_pos).g < x) :
    (hoLv v 0 hv1 hv gv_Om1_pos).l x = x * x * v := by
  rw [hoLv_l hv1 hv gv_Om1_pos hx, mul_zero, add_zero]

theorem ho_hlGt0 : hlGt 0 = 0 := by unfold hlGt; split_ifs <;> rfl

theorem ho_hlGt_le_succ (v : Ordinal.{0}) : hlGt v ≤ hlGt (v + 1) := hlGt_mono (le_add_right le_rfl)

/-- **At an `ε`-number `x`: `hlGt v < x ⇒ hlGt (v+1) < x`.** -/
theorem ho_hlGt_succ_lt {v x : Ordinal.{0}} (hx : InE x) (h : hlGt v < x) : hlGt (v + 1) < x := by
  rcases ho_gt_or h with h' | h'
  · have : v + 1 < ε₀ := hc_eps0_lim.add_one_lt h'
    unfold hlGt; rw [if_pos this]; exact hx.pos
  · exact (hlGt_le _).trans_lt ((ev_isSuccLimit_of_inE hx).add_one_lt h')

/-! ## Levels below the next prefix -/

/-- **A level below the next prefix `Ω₁²·(v+1)`**, with gate at least `hlGt v` and read below `x·x·(v+1)`. -/
def HoGood (v : Ordinal.{0}) (Λ : HnLv) : Prop :=
  Λ.L + Om1 + 1 < Om1 * Om1 * (v + 1) ∧ hlGt v ≤ Λ.g ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x + x < x * x * (v + 1)

theorem ho_band_lt {a v μ : Ordinal.{0}} (ha : InE a) (hμ : μ < a) : a * a * v + a * μ + a + 1 < a * a * (v + 1) := by
  have hl := ev_isSuccLimit_of_inE ha
  have e : a * a * v + a * μ + a + 1 = a * a * v + (a * (μ + 1) + 1) := by
    rw [mul_add_one, ← add_assoc, ← add_assoc]
  rw [e, mul_add_one (a * a) v]
  refine (add_lt_add_iff_left (a * a * v)).2 ?_
  calc a * (μ + 1) + 1 < a * (μ + 1) + a :=
      (add_lt_add_iff_left (a * (μ + 1))).2 (one_lt_omega0.trans (omega0_lt_inE ha))
  _ = a * (μ + 1 + 1) := (mul_add_one a (μ + 1)).symm
  _ < a * a := mul_lt_mul_of_pos_left (hl.add_one_lt (hl.add_one_lt hμ)) ha.pos

/-- **A band level `Ω₁²·v + Ω₁·μ` (`μ < Ω₁`) is below the next prefix.** -/
theorem hoGood_of {Λ : HnLv} {v μ : Ordinal.{0}} (hμ : μ < Om1) (hL : Λ.L = Om1 * Om1 * v + Om1 * μ)
    (hl : ∀ x, Λ.g < x → Λ.l x = x * x * v + x * μ) (hg : hlGt v ≤ Λ.g)
    (hgμ : ∀ x, InE x → x < Om1 → Λ.g < x → μ < x) : HoGood v Λ := by
  refine ⟨?_, hg, fun x hx hx1 hgx => ?_⟩
  · rw [hL]; exact ho_band_lt gl_Om1_E hμ
  · rw [hl x hgx]; exact (lt_add_one _).trans (ho_band_lt hx (hgμ x hx hx1 hgx))

/-- **Every band datum `hoLv v M` is below the next prefix.** -/
theorem hoLv_good {v M : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < Om1) (hM : M < Om1) : HoGood v (hoLv v M hv1 hv hM) :=
  hoGood_of hM rfl (fun _ h => hoLv_l hv1 hv hM h) (le_max_left _ _) (fun _ hx _ h => (hoLv_gt hv1 hv hM hx h).2)

/-- **`x·x·(v+1) < x·x·x`** for `v < x`. -/
theorem ho_next_lt3 {x v : Ordinal.{0}} (hx : InE x) (hv : v < x) : x * x * (v + 1) < x * x * x :=
  mul_lt_mul_of_pos_left ((ev_isSuccLimit_of_inE hx).add_one_lt hv) (mul_pos hx.pos hx.pos)

theorem ho_cube_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x * x * x < lgG x :=
  InE.mul_lt (lgG_facts hx hx1).2.2.2.1 (hl_sq_lt hx hx1) (lgG_facts hx hx1).2.1

theorem ho_cube_one {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) ≤ x * x * x :=
  ((one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (hl_lt_sq hx).le).trans (le_mul_of_one_le_right'
    (one_lt_omega0.trans (omega0_lt_inE hx)).le)

/-! ## The outer low field -/

/-- **The outer low field `φ(x·x·x, Γ_{x+1}+1)`** (`max ω x` for the fixed-point property at every `x`). -/
noncomputable def hoZo (x : Ordinal.{0}) : Ordinal.{0} := veblen (max ω x * max ω x * max ω x) (lgG x + 1)

theorem hoZo_eq {x : Ordinal.{0}} (hx : InE x) : hoZo x = veblen (x * x * x) (lgG x + 1) := by
  unfold hoZo; rw [max_eq_right (omega0_lt_inE hx).le]

theorem hoZo_fix (x : Ordinal.{0}) : veblen 2 (hoZo x) = hoZo x := by
  have h2 : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  have hw : ω ≤ max ω x * max ω x * max ω x :=
    (le_max_left ω x).trans ((le_mul_of_one_le_right' (one_lt_omega0.le.trans (le_max_left ω x))).trans
      (le_mul_of_one_le_right' (one_lt_omega0.le.trans (le_max_left ω x))))
  exact veblen_veblen_of_lt (h2.trans_le hw) _

theorem hoZo_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hoZo x < gq 1 x := by
  rw [hoZo_eq hx, ← hdNx_fixP (hjG_fix hx hx1 (ho_cube_one hx) (ho_cube_lt hx hx1))]
  exact hjG_lt1 hx hx1 (ho_cube_one hx) (ho_cube_lt hx hx1)

/-- **`hdNx a (Γ_{x+1}) < φ(x·x·x, Γ_{x+1}+1)`** for `1 ≤ a < x·x·x`. -/
theorem hoZo_gtG {x a : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (ha1 : 1 ≤ a) (ha : a < x * x * x) :
    hdNx a (lgG x) < hoZo x := by
  rw [hoZo_eq hx, hdNx_fixP (hjG_fix hx hx1 ha1 (ha.trans (ho_cube_lt hx hx1)))]
  exact hd_veb_left_lt ha _

end Googology.Trans.PoR.InaccPsi.R2.Ho
