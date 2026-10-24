import Googology.Trans.PoR.InaccPsi.R2.GiWx

/-!
# THE CODES BELOW `ε_{Ω₁+1}^ω`: Lemma EXACT for every code, and the code system `gwK`

* `gw_eAtomN_pi` (**Lemma EXACT for the atom `ω^{ε_{ρ+1}·(n+1)+β}`** at every pair of bases: `gi_eAtom_pi` for
  `n = 0`, `gw_eAtomK_pi` otherwise), `gw_eNr_pi` (**`π(ε_{ρ+1}^{n+1}·γ(ρ)) = ε_{σ+1}^{n+1}·γ(σ)`**, by the normal
  form of `γ`), `gwR_pi` (**Lemma EXACT for every code below `ε_{Ω₁+1}^ω`**);
* `gw_count` (the codes below `c` with gate below a countable base are countably many: the reading is injective),
  `gwK` (**THE CODE SYSTEM below `ε_{Ω₁+1}^ω`**).

No new axiom.  New definition: `gwK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

/-- **Lemma EXACT for the atom `ω^{ε_{ρ+1}·(n+1)+β}`** at every pair of bases. -/
theorem gw_eAtomN_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ)
    (hβe : β < eN ρ) :
    ω ^ (eN ρ * ((n + 1 : ℕ) : Ordinal.{0}) + β) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * ((n + 1 : ℕ) : Ordinal.{0}) + β)) = ω ^ (eN σ * ((n + 1 : ℕ) : Ordinal.{0}) + pi σ ρ β) := by
  rcases n with _ | m
  · have e : ((0 + 1 : ℕ) : Ordinal.{0}) = 1 := by norm_num
    rw [e, mul_one, mul_one]
    exact gi_eAtom_pi hB hβTB hβe
  · have e : ((m + 1 + 1 : ℕ) : Ordinal.{0}) = ((m + 2 : ℕ) : Ordinal.{0}) := rfl
    rw [e]
    exact gw_eAtomK_pi hB m hβTB hβe

/-- **`π(ε_{ρ+1}^{n+1}·γ(ρ)) = ε_{σ+1}^{n+1}·γ(σ)`** at every pair of bases, for every code `γ < ε_{Ω₁+1}` with gate
below `σ`. -/
theorem gw_eNr_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) : ∀ γ, γ < gfE → gtc γ < σ →
    eN ρ ^ ((n + 1 : ℕ) : Ordinal.{0}) * rdc γ ρ ∈ TB ρ σ ∧
      pi σ ρ (eN ρ ^ ((n + 1 : ℕ) : Ordinal.{0}) * rdc γ ρ) = eN σ ^ ((n + 1 : ℕ) : Ordinal.{0}) * rdc γ σ := by
  have hσE := hB.1
  have hρE := hB.2.1
  have h0T : (0 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB hσE.pos
  have h0pi : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
  set N : Ordinal.{0} := ((n + 1 : ℕ) : Ordinal.{0}) with hN
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγW hg
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [rdc_zero, rdc_zero, mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
  obtain ⟨-, hqΩ, -, -, hrγ, -⟩ := parts hγ0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hγ0 hγW
  have hl := log_lt hγ0 hγW
  set l := log Om1 γ with hldef
  set q := γ / Om1 ^ l with hqdef
  set r := γ % Om1 ^ l with hrdef
  obtain ⟨h1, h2⟩ := IH r hrγ (hrγ.trans hγW) (gr.trans_lt hg)
  have hqσ : q < σ := gq.trans_lt hg
  have hcb : OT.CB (tcx l) σ := cb_tcx hσE.pos l (gl.trans_lt hg)
  have edec : ∀ x, InE x → eN x ^ N * rdc γ x = ω ^ (eN x * N + OT.ev (tcx l) x) * q + eN x ^ N * rdc r x := by
    intro x hx
    rw [rdc_dec hγ0 hγW, mul_add, ← mul_assoc, pw_eq' hx, gw_eNpow, ← opow_add, ev_tcx hx]
  have hatom : ∀ z, z < σ → ω ^ (eN ρ * N + (OT.ev (tcx l) ρ + z)) ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * N + (OT.ev (tcx l) ρ + z))) = ω ^ (eN σ * N + (OT.ev (tcx l) σ + z)) := by
    intro z hz
    have hcb' : OT.CB (OT.add (tcx l) (OT.k z)) σ := ⟨hcb, hz⟩
    obtain ⟨t1, t2⟩ := pi_ev hB _ hcb'
    simp only [OT.ev_add, OT.ev_k] at t1 t2
    have hlt : OT.ev (tcx l) ρ + z < eN ρ := by
      have := ev_lt_eN (OT.CB_mono hcb' hB.2.2.1.le)
      simpa only [OT.ev_add, OT.ev_k] using this
    obtain ⟨t3, t4⟩ := gw_eAtomN_pi hB n t1 hlt
    rw [t2] at t4
    exact ⟨t3, t4⟩
  have hmul : ∀ q', q' < σ → ω ^ (eN ρ * N + OT.ev (tcx l) ρ) * q' ∈ TB ρ σ ∧
      pi σ ρ (ω ^ (eN ρ * N + OT.ev (tcx l) ρ) * q') = ω ^ (eN σ * N + OT.ev (tcx l) σ) * q' := by
    intro q'
    induction q' using WellFoundedLT.induction with
    | ind q' IHq =>
    intro hq'
    rcases eq_or_ne q' 0 with rfl | hq0
    · rw [mul_zero, mul_zero]; exact ⟨h0T, h0pi⟩
    obtain ⟨q'', hgs, -, hq''⟩ := lg_split hq0
    have hz : lg q' < σ := lt_of_le_of_lt (lg_le hq0) hq'
    obtain ⟨k1, k2⟩ := IHq q'' hq'' (hq''.trans hq')
    obtain ⟨k3, k4⟩ := hatom _ hz
    rw [hgs, mul_add, mul_add, ← opow_add, ← opow_add, add_assoc, add_assoc]
    obtain ⟨k5, k6⟩ := pi_add hB k1 k3
    exact ⟨k5, by rw [k6, k2, k4]⟩
  obtain ⟨m1, m2⟩ := hmul q hqσ
  rw [edec ρ hρE, edec σ hσE]
  obtain ⟨m3, m4⟩ := pi_add hB m1 h1
  exact ⟨m3, by rw [m4, m2, h2]⟩

/-- **Lemma EXACT for every code `c < ε_{Ω₁+1}^ω`** at every pair of bases above its gate. -/
theorem gwR_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : ∀ c, c < gwB → gwG c < σ →
    gwR c ρ ∈ TB ρ σ ∧ pi σ ρ (gwR c ρ) = gwR c σ := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [gwG_low hcE] at hg
    rw [gwR_low hcE, gwR_low hcE]
    exact rdc_pi hB hcE hg
  obtain ⟨hk, -, hdE, -, -⟩ := gw_parts hcE
  obtain ⟨g1, g2⟩ := gw_parts_g hB.1 hcE hg
  obtain ⟨n, hn⟩ := gw_nat_of_lt hc hcE
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    have : n ≠ 0 := by rintro rfl; exact hk (by rw [hn, Nat.cast_zero])
    omega⟩
  have hrc : c % gfE ^ log gfE c < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  obtain ⟨h1, h2⟩ := IH _ hrc (hrc.trans hc) g2
  rw [hn] at hdE g1
  obtain ⟨h3, h4⟩ := gw_eNr_pi hB m _ hdE g1
  rw [gwR_dec hcE, gwR_dec hcE, hn]
  rw [hn] at h1 h2
  obtain ⟨h5, h6⟩ := pi_add hB h3 h1
  exact ⟨h5, by rw [h6, h4, h2]⟩

/-- **The codes below `c ≤ ε_{Ω₁+1}^ω` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
theorem gw_count {c y : Ordinal.{0}} (hc : c ≤ gwB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // gwG b.1 < y} := by
  have hq1 : gq 0 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gfq0_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // gwG b.1 < y} → Iio (gq 0 y) := fun b =>
    ⟨gwR b.1.1 y, gwR_lt0 hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : gwR b.1.1 y = gwR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (gwR_mono hy _ b'.2 _ h b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (gwR_mono hy _ b.2 _ h b'.2).ne'

theorem gwB_lt_G0 : gwB < gcG 0 := by
  have hE : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)
  rw [gwB_eq]
  have := (opow_lt_opow_iff_right one_lt_omega0).2 (gcG_ghE_lt 0)
  rwa [show ω ^ gcG 0 = gcG 0 from hE] at this

/-- **THE CODE SYSTEM below `ε_{Ω₁+1}^ω`.** -/
noncomputable def gwK : GiCS where
  B := gwB
  gt := gwG
  B_lt := gwB_lt_G0
  gt_zero := gwG_zero
  gt_lt := gwG_lt_Om1
  gt_succ := fun b _ hZ _ hg => gwG_succ hZ b hg
  mem := fun _ _ _ c hc hg => gw_mem c hc hg
  B_mem := fun _ _ _ => gwB_mem
  code_gate := fun _ _ hZ1 hZ0 hZa hZp hAt _ hc hcB => gw_code_gate hZ1 hZ0 hZa hZp hAt hc hcB
  count := fun _ _ hc hy hy1 => gw_count hc hy hy1

theorem gwK_B : gwK.B = gwB := rfl

theorem gwK_gt : gwK.gt = gwG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gi
