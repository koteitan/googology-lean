import Googology.Trans.PoR.InaccPsi.R2.GiUnif

/-!
# THE CODE SYSTEM BELOW `ε_{Ω₁+1}²`: the codes `ε_{Ω₁+1}·γ + a` (`γ, a < ε_{Ω₁+1}`)

Every `c < ε_{Ω₁+1}·ε_{Ω₁+1}` is `ε_{Ω₁+1}·γ + a` with `γ = c / ε_{Ω₁+1}`, `a = c mod ε_{Ω₁+1}` codes below
`ε_{Ω₁+1}` (`R2.GfSub`).  Its gate is the larger of the gates of `γ` (taken `0` when `γ < ω`, so that below
`ε_{Ω₁+1}·ω` it is the gate `Gh.ghg` of `R2.GhAt`) and of `a`.

* `giQ`, `giB` (`ε_{Ω₁+1}²`), `giG` (the gate), `gi_div_small`, `gi_div_big` (the quotient of a sum);
* `gi_code_gate` (**a code `c < ε_{Ω₁+1}²` over `Z`, all atoms above `ε_{Ω₁+1}²`, has its gate below `Z`**: by induction
  on the code; the only `ε`-number in `[ε_{Ω₁+1}, ε_{Ω₁+1}²)` is `ε_{Ω₁+1}`, and `ω^y ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}²)` is
  `ε_{Ω₁+1}·ω^{y'}`, `y = ε_{Ω₁+1} + y'`);
* `gi_mulE_mem` (`ε_{Ω₁+1}·γ` lies in every hull containing the digits of `γ`), `gi_mem`, `giB_mem`, `gi_count`,
  `giG_succ`;
* `giK` (**THE CODE SYSTEM**), `giK_B`, `giK_gt`, `giG_lt_E` (below `ε_{Ω₁+1}` the gate is `gtc`).

No new axiom.  New definitions: `giQ`, `giB`, `giG`, `giK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The gate of a quotient**: `0` below `ω`, else `gtc`. -/
noncomputable def giQ (q : Ordinal.{0}) : Ordinal.{0} := if q < ω then 0 else gtc q

/-- **The bound**: `ε_{Ω₁+1}²`. -/
noncomputable def giB : Ordinal.{0} := gfE * gfE

/-- **The gate of a code** `ε_{Ω₁+1}·γ + a`. -/
noncomputable def giG (c : Ordinal.{0}) : Ordinal.{0} := max (giQ (c / gfE)) (gtc (c % gfE))

theorem giQ_le (q : Ordinal.{0}) : giQ q ≤ gtc q := by
  unfold giQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem giQ_zero : giQ 0 = 0 := by unfold giQ; rw [if_pos omega0_pos]

theorem giQ_one : giQ 1 = 0 := by unfold giQ; rw [if_pos one_lt_omega0]

theorem gtc_lt_of_giQ {q y : Ordinal.{0}} (hy : ω < y) (h : giQ q < y) : q < gfE → gtc q < y := by
  intro hq
  unfold giQ at h
  split_ifs at h with hω
  · rw [(rdc_const (hω.trans omega_lt_Om1) 0).2]; exact hω.trans hy
  · exact h

theorem giB_eq : giB = ω ^ (gfE + gfE) := by
  rw [giB, opow_add, show ω ^ gfE = gfE from eW_E]

theorem gi_div_lt {c : Ordinal.{0}} (hc : c < giB) : c / gfE < gfE := (Ordinal.div_lt gfE_ne).2 hc

theorem gi_dec (c : Ordinal.{0}) : gfE * (c / gfE) + c % gfE = c := Ordinal.div_add_mod c gfE

theorem gfE_lt_giB : gfE < giB := lt_mul_of_one_lt_right eW_E.pos (gf_one_lt_Om1.trans Om1_lt_eW)

theorem giB_lt_eN : giB < eN gfE := by
  rw [giB_eq]
  have h : gfE + gfE < eN gfE := (inE_indec (eN_E gfE)).add_lt (lt_eN gfE) (lt_eN gfE)
  have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 h
  rwa [show ω ^ eN gfE = eN gfE from eN_E gfE] at h2

/-- The quotient of a sum whose right summand is below `ε_{Ω₁+1}`. -/
theorem gi_div_small (u : Ordinal.{0}) {v : Ordinal.{0}} (hv : v < gfE) : (u + v) / gfE = u / gfE := by
  have e : u + v = gfE * (u / gfE) + (u % gfE + v) := by
    conv_lhs => rw [← Ordinal.div_add_mod u gfE]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_div _ gfE_ne, Ordinal.div_eq_zero_of_lt (eW_indec.add_lt (gh_mod_lt u) hv), add_zero]

/-- The quotient of a sum whose right summand is at least `ε_{Ω₁+1}`. -/
theorem gi_div_big (u : Ordinal.{0}) {v : Ordinal.{0}} (hv : gfE ≤ v) : (u + v) / gfE = u / gfE + v / gfE := by
  have hq : 1 ≤ v / gfE := by
    rw [Order.one_le_iff_pos, Ordinal.div_pos gfE_ne]; exact hv
  have e1 : v / gfE = 1 + (v / gfE - 1) := (Ordinal.add_sub_cancel_of_le hq).symm
  have hab : u % gfE + gfE = gfE := Ordinal.add_absorp (b := gfE)
    (by rw [show ω ^ gfE = gfE from eW_E]; exact gh_mod_lt u) (by rw [show ω ^ gfE = gfE from eW_E])
  have e2 : u % gfE + gfE * (v / gfE) = gfE * (v / gfE) := by
    rw [e1, mul_add, mul_one, ← add_assoc, hab]
  have e : u + v = gfE * (u / gfE + v / gfE) + v % gfE := by
    conv_lhs => rw [← Ordinal.div_add_mod u gfE, ← Ordinal.div_add_mod v gfE]
    rw [add_assoc, ← add_assoc (u % gfE), e2, ← add_assoc, ← mul_add]
  rw [e, Ordinal.mul_add_div _ gfE_ne, Ordinal.div_eq_zero_of_lt (gh_mod_lt v), add_zero]

theorem giG_lt_E {c : Ordinal.{0}} (hc : c < gfE) : giG c = gtc c := by
  rw [giG, Ordinal.div_eq_zero_of_lt hc, Ordinal.mod_eq_of_lt hc, giQ_zero, max_eq_right zero_le]

theorem giG_zero : giG 0 = 0 := by rw [giG_lt_E eW_E.pos, gtc_zero]

theorem giG_E : giG gfE = 0 := by
  rw [giG, Ordinal.div_self gfE_ne, Ordinal.mod_self, giQ_one, gtc_zero, max_self]

theorem giG_lt_Om1 {c : Ordinal.{0}} (hc : c < giB) : giG c < Om1 :=
  max_lt ((giQ_le _).trans_lt (gtc_lt_Om1 _ (gi_div_lt hc))) (gtc_lt_Om1 _ (gh_mod_lt c))

/-- The gates of the parts of a code are below `y > ω` once its gate is. -/
theorem giG_parts {c y : Ordinal.{0}} (hc : c < giB) (hy : ω < y) (h : giG c < y) :
    gtc (c / gfE) < y ∧ gtc (c % gfE) < y :=
  ⟨gtc_lt_of_giQ hy ((le_max_left _ _).trans_lt h) (gi_div_lt hc), (le_max_right _ _).trans_lt h⟩

/-- **The gate of a code below `ε_{Ω₁+1}²`**: a code over `Z` (atoms above `ε_{Ω₁+1}²`) has its gate below `Z`. -/
theorem gi_code_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, giB < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < giB → giG c < Z := by
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => gfE_lt_giB.trans (hAt s hs)
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gfE → giG x < Z := fun x hx h => by
    rw [giG_lt_E h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  have hq : ∀ q, gtc q < Z → giQ q < Z := fun q h => (giQ_le q).trans_lt h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    have hxB : x < giB := lt_of_le_of_lt le_self_add h
    have hyB : y < giB := lt_of_le_of_lt le_add_self h
    obtain ⟨gx1, gx2⟩ := giG_parts hxB hωZ (ihx hxB)
    obtain ⟨gy1, gy2⟩ := giG_parts hyB hωZ (ihy hyB)
    rcases lt_or_ge y gfE with hy' | hy'
    · rw [giG, gi_div_small x hy', gh_mod_small x hy']
      rw [Ordinal.mod_eq_of_lt hy'] at gy2
      exact max_lt (hq _ gx1) (gtc_add hZa _ _ (gh_mod_lt x) hy' gx2 gy2)
    · rw [giG, gi_div_big x hy', gh_mod_big x hy']
      exact max_lt (hq _ (gtc_add hZa _ _ (gi_div_lt hxB) (gi_div_lt hyB) gx1 gy1)) gy2
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h hge ⊢
      have hyB : y < giB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
      have hEy : gfE ≤ y := by
        rw [← show ω ^ gfE = gfE from eW_E] at hge
        exact (opow_le_opow_iff_right one_lt_omega0).1 hge
      have hyEE : y < gfE + gfE := by
        rw [giB_eq] at h; exact (opow_lt_opow_iff_right one_lt_omega0).1 h
      set y' := y - gfE with hy'
      have ey : y = gfE + y' := (Ordinal.add_sub_cancel_of_le hEy).symm
      have hy'E : y' < gfE := by rw [ey] at hyEE; exact (add_lt_add_iff_left _).1 hyEE
      have ew : ω ^ y = gfE * ω ^ y' := by rw [ey, opow_add, show ω ^ gfE = gfE from eW_E]
      have hmod : y % gfE = y' := by
        rw [ey, gh_mod_small gfE hy'E, Ordinal.mod_self, zero_add]
      obtain ⟨-, gy2⟩ := giG_parts hyB hωZ (ihy hyB)
      rw [hmod] at gy2
      rw [ew, giG, Ordinal.mul_div_cancel _ gfE_ne, Ordinal.mul_mod, gtc_zero]
      exact max_lt (hq _ (gtc_opow hZw hy'E gy2)) hZ0
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have heq : veblen x y = gfE := by
        rcases hge.lt_or_eq with hlt | heq
        · exact absurd ((eN_le hlt hE).trans_lt h) (not_lt.2 giB_lt_eN.le)
        · exact heq.symm
      rw [heq, giG_E]; exact hZ0

/-- **`ε_{Ω₁+1}·γ` lies in every hull containing the digits of `γ`.** -/
theorem gi_mulE_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} :
    ∀ q, q < gfE → gtc q < b → gfE * q ∈ S.CSet a b := by
  have hE : gfE ∈ S.CSet a b := gfW_inC
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hqW hg
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨-, -, -, hdec, hrq, -⟩ := parts hq0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hq0 hqW
  have hlq := log_lt hq0 hqW
  obtain ⟨-, hlO⟩ := gfW_mem (S := S) (a := a) (b := b) _ (hlq.trans hqW) (gl.trans_lt hg)
  have hr := IH _ hrq (hrq.trans hqW) (gr.trans_lt hg)
  have e : gfE * q = ω ^ (gfE + Om1 * log Om1 q) * (q / Om1 ^ log Om1 q) + gfE * (q % Om1 ^ log Om1 q) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, opow_add, ← Om1_pow_eq, show ω ^ gfE = gfE from eW_E]
  rw [e]
  exact CSet.add_mem (gfMul_mem (CSet.add_mem hE hlO) _ (gq.trans_lt hg)) hr

/-- **Every code `c < ε_{Ω₁+1}²` lies in every hull containing its gate**, `Ω₁` being in the hull. -/
theorem gi_mem {S : InaccSeq.{0}} {a b c : Ordinal.{0}} (hc : c < giB) (hg : giG c < b) : c ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  have hb : Om1 < b ∨ b ≤ Om1 := lt_or_ge Om1 b
  rw [← gi_dec c]
  refine CSet.add_mem ?_ (gfW_mem' (gh_mod_lt c) ((le_max_right _ _).trans_lt hg))
  have hq := gi_div_lt hc
  by_cases hω : c / gfE < ω
  · obtain ⟨n, hn⟩ := lt_omega0.1 hω
    rw [hn]; exact lg_cset_mul_nat gfW_inC n
  · have h1 : giQ (c / gfE) = gtc (c / gfE) := by unfold giQ; rw [if_neg hω]
    exact gi_mulE_mem _ hq (h1 ▸ (le_max_left _ _).trans_lt hg)

theorem giB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : giB ∈ S.CSet a b := by
  rw [giB_eq]
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.add_mem (gfW_inC (S := S) (a := a) (b := b)) gfW_inC)
  rwa [veblen_zero_apply] at this

/-- **The codes below `c ≤ ε_{Ω₁+1}²` with gate below `y < Ω₁` are countably many.** -/
theorem gi_count {c y : Ordinal.{0}} (hc : c ≤ giB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // giG b.1 < y} := by
  have hyn : eN y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact Ge.eN_lt_Om1' hy hy1
  haveI := Gc.gc_countable hyn
  have hωy := omega0_lt_inE hy
  have hB : ∀ b : {b : Iio c // giG b.1 < y}, b.1.1 < giB := fun b => lt_of_lt_of_le b.1.2 hc
  let f : {b : Iio c // giG b.1 < y} → Iio (eN y) × Iio (eN y) := fun b =>
    (⟨rdc (b.1.1 / gfE) y, rdc_lt_eN hy _ (giG_parts (hB b) hωy b.2).1⟩,
      ⟨rdc (b.1.1 % gfE) y, rdc_lt_eN hy _ (giG_parts (hB b) hωy b.2).2⟩)
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e1 : rdc (b.1.1 / gfE) y = rdc (b'.1.1 / gfE) y := congrArg (fun p => p.1.1) hbb
  have e2 : rdc (b.1.1 % gfE) y = rdc (b'.1.1 % gfE) y := congrArg (fun p => p.2.1) hbb
  obtain ⟨g1, g2⟩ := giG_parts (hB b) hωy b.2
  obtain ⟨g1', g2'⟩ := giG_parts (hB b') hωy b'.2
  have e3 : b.1.1 / gfE = b'.1.1 / gfE := by
    rcases lt_trichotomy (b.1.1 / gfE) (b'.1.1 / gfE) with h | h | h
    · exact absurd e1 (rdc_mono hy (gi_div_lt (hB b')) h g1' g1).ne
    · exact h
    · exact absurd e1 (rdc_mono hy (gi_div_lt (hB b)) h g1 g1').ne'
  have e4 : b.1.1 % gfE = b'.1.1 % gfE := by
    rcases lt_trichotomy (b.1.1 % gfE) (b'.1.1 % gfE) with h | h | h
    · exact absurd e2 (rdc_mono hy (gh_mod_lt _) h g2' g2).ne
    · exact h
    · exact absurd e2 (rdc_mono hy (gh_mod_lt _) h g2 g2').ne'
  refine Subtype.ext (Subtype.ext ?_)
  rw [← gi_dec b.1.1, ← gi_dec b'.1.1, e3, e4]

theorem giG_succ {b Z : Ordinal.{0}} (hZ : IsSuccLimit Z) (hg : giG b < Z) : giG (b + 1) < Z := by
  have h1 : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  rw [giG, gi_div_small b h1, gh_mod_small b h1]
  exact max_lt ((le_max_left _ _).trans_lt hg)
    ((rdc_succ _ (gh_mod_lt b) 0).2.2.trans_lt (hZ.add_one_lt ((le_max_right _ _).trans_lt hg)))

theorem giB_lt_G0 : giB < gcG 0 := by
  have hE : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)
  exact hE.mul_lt (gcG_eW_lt 0) (gcG_eW_lt 0)

/-- **THE CODE SYSTEM below `ε_{Ω₁+1}²`.** -/
noncomputable def giK : GiCS where
  B := giB
  gt := giG
  B_lt := giB_lt_G0
  gt_zero := giG_zero
  gt_lt := fun _ hc => giG_lt_Om1 hc
  gt_succ := fun _ _ hZ _ hg => giG_succ hZ hg
  mem := fun _ _ _ _ hc hg => gi_mem hc hg
  B_mem := fun _ _ _ => giB_mem
  code_gate := fun _ _ hZ1 hZ0 hZa hZp hAt _ hc hcB => gi_code_gate hZ1 hZ0 hZa hZp hAt hc hcB
  count := fun _ _ hc hy hy1 => gi_count hc hy hy1

theorem giK_B : giK.B = giB := rfl

theorem giK_gt : giK.gt = giG := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gi
