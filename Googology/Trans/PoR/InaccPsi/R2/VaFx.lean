import Googology.Trans.PoR.InaccPsi.R2.VaSeg

/-!
# VaFx: THE FIXED POINTS OF `Γ` AS CODES — THE GATES OF THEIR PARTS

A fixed-point atom `e` (`¬ yhJ e < e`) below `X` is `F_λ(y)` with `1 ≤ λ = tlLev e`, `y = tlI λ e` not a fixed point
of `F_λ`; its reading is `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` with `K = f(x) + (y − (f+1))(x)` past the largest fixed point
`f < y` of `F_λ` and `K = (y − y₀(λ))(x)` below the first.  Its gate is `max (yrQ λ) (yrQ (y − y₀(λ)))`
(`Yr.yrQE_atom_fixL`); every part keeps it up to `ω`.

* `vs_fixatom` (**a fixed-point atom is a fixed point of `Γ`**), `vs_fix_data`;
* `vsMx` (the largest point of a class in `(Ω₁, c]`), `vs_mx_le`, `vs_mx_ge`, `vs_mx_eq`, `vs_mx_gate` (**the largest
  point of a closed class of fixed points of `Γ` keeps the gate of `c` up to `ω`**);
* `vs_fpL_eq`, `vs_fpL_mem`, `vs_fpL_gate`; `vs_fix_gate_l`, `vs_fix_gate_f`, `vs_fix_gate_0` (**the parts of a
  fixed point keep its gate**).

No new axiom.  New definition: `vsMx`.
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
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## Fixed-point atoms -/

/-- **A fixed-point atom** (`¬ yhJ e < e`) **is a fixed point of `Γ`.** -/
theorem vs_fixatom {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) : gamma e = e := by
  obtain ⟨j, rfl⟩ := yhAt_iff.1 hA
  rw [yhJ_gcG] at hi
  have hjj : j = gcG j := le_antisymm (gcG_strictMono.le_apply) (not_lt.1 hi)
  have hE : InE (gcG j) := Low.opow_eq_self_of_SC (gcG_SC j)
  have hjE : InE j := by rw [hjj]; exact hE
  have hjO : Om1 < j := by rw [hjj]; exact hA.2
  have h1 : Om1 + 1 + j = j := gl_absorb hjE hjO
  rw [← hjj]
  conv_lhs => rw [← h1]
  rw [← tf_gcG]; exact hjj.symm

/-- **The data of a fixed-point atom below `X`**: `e = F_λ(y)`, `1 ≤ λ < e`, `y < e`, `y` not a fixed point of `F_λ`. -/
theorem vs_fix_data {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (heX : e < tlX) :
    1 ≤ tlLev e ∧ tlLev e < e ∧ tlI (tlLev e) e < e ∧ rhF (tlLev e) (tlI (tlLev e) e) = e ∧
      rhF (tlLev e) (tlI (tlLev e) e) ≠ tlI (tlLev e) e := by
  obtain ⟨hnf, hyc, hlc⟩ := tl_nf hA.1 hA.2 heX
  obtain ⟨-, hne, -⟩ := tlLev_spec hA.1 hA.2 heX
  refine ⟨one_le_iff_ne_zero.2 fun h0 => hne ?_, hlc, hyc, hnf, by rw [hnf]; exact (ne_of_gt hyc)⟩
  rw [h0, rhF_zero]; exact vs_fixatom hA hi

/-! ## The largest point of a class -/

/-- **The largest point of a class `P` in `(Ω₁, c]`.** -/
noncomputable def vsMx (P : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Ordinal.{0} :=
  sSup {f | P f ∧ Om1 < f ∧ f ≤ c}

theorem vs_mx_le (P : Ordinal.{0} → Prop) {c : Ordinal.{0}} (h : ∃ f, P f ∧ Om1 < f ∧ f ≤ c) : vsMx P c ≤ c :=
  csSup_le h fun _ hf => hf.2.2

theorem vs_mx_ge (P : Ordinal.{0} → Prop) {c f : Ordinal.{0}} (hf : P f) (hOf : Om1 < f) (hfc : f ≤ c) :
    f ≤ vsMx P c :=
  le_csSup ⟨c, fun _ h => h.2.2⟩ (show f ∈ {f | P f ∧ Om1 < f ∧ f ≤ c} from ⟨hf, hOf, hfc⟩)

/-- **No point of `P` in `(b, c]`**: the largest points agree. -/
theorem vs_mx_eq (P : Ordinal.{0} → Prop) {b c : Ordinal.{0}} (hbc : b ≤ c)
    (hnone : ∀ f, P f → Om1 < f → f ≤ c → f ≤ b) : vsMx P b = vsMx P c := by
  unfold vsMx; congr 1; ext f
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.trans hbc⟩, fun h => ⟨h.1, h.2.1, hnone f h.1 h.2.1 h.2.2⟩⟩

/-- **The largest point of a closed class of fixed points of `Γ` keeps the gate of `c` up to `ω`** (a fixed-point
atom outside the class has the points of the class below it below its index). -/
theorem vs_mx_gate (P : Ordinal.{0} → Prop) (hfix : ∀ f, P f → gamma f = f)
    (hmem : ∀ c, (∃ f, P f ∧ Om1 < f ∧ f ≤ c) → P (vsMx P c))
    (hat : ∀ e, YhAt e → ¬ yhJ e < e → ¬ P e → e < tlX → ∀ f, P f → f < e → f ≤ tlI (tlLev e) e) :
    ∀ c, c < tlX → (∃ f, P f ∧ Om1 < f ∧ f ≤ c) → yrG (vsMx P c) ≤ max ω (yrG c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcX hex
  obtain ⟨f₀, hP₀, hO₀, hf₀⟩ := hex
  have hfE : ∀ f, P f → InE f := fun f hf => zm_fix_E (zm_fix_of_gamma (hfix f hf))
  have hBc : tfBG ≤ c := (tfBG_le (hfix f₀ hP₀) hO₀).trans hf₀
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hBc
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  have hPe : ∀ f, P f → Om1 < f → f ≤ c → f ≤ guE c := fun f hf _ hfc => by
    by_contra h
    push Not at h
    exact absurd (hfc.trans_lt hce) (not_lt.2 (eN_le h (hfE f hf)))
  have hFF : vsMx P (guE c) = vsMx P c := vs_mx_eq P hec hPe
  have hge : yrG (guE c) ≤ yrG c := by
    rw [yrG_base heE hGe, yrG_dec hGc]; exact (le_max_left _ _).trans (le_max_left _ _)
  rcases hec.lt_or_eq with hlt | heq
  · rw [← hFF]
    exact (IH _ hlt (hlt.trans hcX) ⟨f₀, hP₀, hO₀, hPe f₀ hP₀ hO₀ hf₀⟩).trans (max_le_max le_rfl hge)
  have hcE : InE c := by rw [← heq]; exact heE
  have hcl : yrG c = yrQE c := yrG_base hcE hGc
  by_cases hPc : P c
  · have h : vsMx P c = c :=
      le_antisymm (vs_mx_le P ⟨f₀, hP₀, hO₀, hf₀⟩) (vs_mx_ge P hPc (tfBG_gt.trans_le hBc) le_rfl)
    rw [h]; exact le_max_right _ _
  by_cases hA : YhAt c
  · by_cases hi : yhJ c < c
    · -- a non-fixed atom `Γ(j)`: the points of `P` below it are below `j`
      have hj : ∀ f, P f → Om1 < f → f ≤ c → f ≤ yhJ c := fun f hf hOf hfc => by
        obtain ⟨j, hj⟩ := yhAt_iff.1 hA
        have h1 : gcG f ≤ gcG j := by rw [vs_gcG_fix (hfix f hf) hOf, ← hj]; exact hfc
        rw [hj, yhJ_gcG]; exact gcG_strictMono.le_iff_le.1 h1
      rw [← vs_mx_eq P hi.le hj]
      refine (IH _ hi (hi.trans hcX) ⟨f₀, hP₀, hO₀, hj f₀ hP₀ hO₀ hf₀⟩).trans ?_
      rw [va_maxQ le_rfl (yhJ c), hcl, yrQE_atom hA hi]
    · -- a fixed-point atom outside `P`: the points of `P` below it are below its index
      obtain ⟨hnf, hyc, hlc⟩ := tl_nf hA.1 hA.2 hcX
      have hL : tlLev c < c ∧ tlI (tlLev c) c < c := ⟨hlc, hyc⟩
      have hy : ∀ f, P f → Om1 < f → f ≤ c → f ≤ tlI (tlLev c) c := fun f hf _ hfc => by
        rcases hfc.lt_or_eq with h | h
        · exact hat c hA hi hPc hcX f hf h
        · exact absurd (h ▸ hf) hPc
      have hf₀y := hy f₀ hP₀ hO₀ hf₀
      rw [← vs_mx_eq P hyc.le hy]
      refine (IH _ hyc (hyc.trans hcX) ⟨f₀, hP₀, hO₀, hf₀y⟩).trans ?_
      have hsub : tlI (tlLev c) c - glY0 (tlLev c) = tlI (tlLev c) c :=
        Ordinal.sub_eq_of_add_eq (gl_absorb_le (hfE f₀ hP₀) hO₀ hf₀y)
      rw [va_maxQ le_rfl (tlI (tlLev c) c), hcl, yrQE_atom_fixL hA hi hL, hsub]
      exact max_le_max le_rfl (le_max_right _ _)
  · -- not an atom: the largest point of `P` is below the level or the index
    have hGc' : gcG 0 < c := lt_of_le_of_ne hGc fun h => hA (h ▸ yhAt_gcG 0)
    obtain ⟨-, hkc, hic, hpsi⟩ := va_data hcE hGc' hA
    have hex : ∃ f, P f ∧ Om1 < f ∧ f ≤ c := ⟨f₀, hP₀, hO₀, hf₀⟩
    have hPF := hmem c hex
    have hOF : Om1 < vsMx P c := hO₀.trans_le (vs_mx_ge P hP₀ hO₀ hf₀)
    have hFSC : SC (vsMx P c) := by rw [← hfix _ hPF]; exact Lq.lq_gamma_SC _
    have hcle : vsMx P c ≤ yhK c ∨ vsMx P c ≤ yhI c := by
      by_contra hcon
      push Not at hcon
      have h := yhPsi_lt_SC hFSC hOF hcon.1 hcon.2
      rw [hpsi] at h
      exact absurd (vs_mx_le P hex) (not_le.2 h)
    have hQ : max ω (yrG c) = max ω (max (yrQ (yhK c)) (yrQ (yhI c))) := by rw [hcl, yrQE_psi hA]
    rw [hQ]
    rcases hcle with h | h
    · have hb : ∀ f, P f → Om1 < f → f ≤ c → f ≤ yhK c := fun f hf hOf hfc =>
        (vs_mx_ge P hf hOf hfc).trans h
      rw [← vs_mx_eq P hkc.le hb]
      refine (IH _ hkc (hkc.trans hcX) ⟨f₀, hP₀, hO₀, hb f₀ hP₀ hO₀ hf₀⟩).trans ?_
      rw [va_maxQ le_rfl (yhK c)]
      exact max_le_max le_rfl (le_max_left _ _)
    · have hb : ∀ f, P f → Om1 < f → f ≤ c → f ≤ yhI c := fun f hf hOf hfc =>
        (vs_mx_ge P hf hOf hfc).trans h
      rw [← vs_mx_eq P hic.le hb]
      refine (IH _ hic (hic.trans hcX) ⟨f₀, hP₀, hO₀, hb f₀ hP₀ hO₀ hf₀⟩).trans ?_
      rw [va_maxQ le_rfl (yhI c)]
      exact max_le_max le_rfl (le_max_right _ _)

/-! ## The largest fixed point of `F_λ` below the index -/

theorem vs_fpL_eq {l y : Ordinal.{0}} (hy : rhF l y ≠ y) : vaFpL l y = vsMx (fun f => rhF l f = f) y := by
  unfold vaFpL vsMx; congr 1; ext f
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.le⟩, fun h => ⟨h.1, h.2.1, lt_of_le_of_ne h.2.2 fun e => hy (e ▸ h.1)⟩⟩

/-- The fixed points of `F_λ` above `Ω₁` are closed under suprema. -/
theorem vs_fpL_closed (l c : Ordinal.{0}) (hc : ∃ f, rhF l f = f ∧ Om1 < f ∧ f ≤ c) :
    rhF l (vsMx (fun f => rhF l f = f) c) = vsMx (fun f => rhF l f = f) c := by
  unfold vsMx
  show rhF l (sSup {f | rhF l f = f ∧ Om1 < f ∧ f ≤ c}) = sSup {f | rhF l f = f ∧ Om1 < f ∧ f ≤ c}
  rw [(rhF_normal l).map_sSup (s := {f | rhF l f = f ∧ Om1 < f ∧ f ≤ c}) hc ⟨c, fun _ h => h.2.2⟩]
  congr 1
  ext f
  constructor
  · rintro ⟨f', hf', rfl⟩
    have h1 : rhF l f' = f' := hf'.1
    rw [h1]; exact hf'
  · intro hf; exact ⟨f, hf, hf.1⟩

/-- **The largest fixed point `f < y` of `F_λ`**: a fixed point of `F_λ` in `(Ω₁, y)`. -/
theorem vs_fpL_mem {l y : Ordinal.{0}} (hy : rhF l y ≠ y) (hF : VaFixL l y) :
    rhF l (vaFpL l y) = vaFpL l y ∧ Om1 < vaFpL l y ∧ vaFpL l y < y := by
  obtain ⟨f, hf, hOf, hfy⟩ := hF
  have hex : ∃ f, rhF l f = f ∧ Om1 < f ∧ f ≤ y := ⟨f, hf, hOf, hfy.le⟩
  have hfix := vs_fpL_closed l y hex
  rw [vs_fpL_eq hy]
  refine ⟨hfix, hOf.trans_le (vs_mx_ge _ hf hOf hfy.le), lt_of_le_of_ne (vs_mx_le _ hex) fun e => hy ?_⟩
  rw [← e]; exact hfix

/-- **The largest fixed point of `F_λ` below `y` keeps the gate of `y` up to `ω`.** -/
theorem vs_fpL_gate {l y : Ordinal.{0}} (hy : rhF l y ≠ y) (hyX : y < tlX) (hF : VaFixL l y) :
    yrG (vaFpL l y) ≤ max ω (yrG y) := by
  rw [vs_fpL_eq hy]
  refine vs_mx_gate (fun f => rhF l f = f) (fun f hf => ?_) (fun c hc => vs_fpL_closed l c hc)
    (fun e hA hi hPe heX f hf hfe => ?_) y hyX ?_
  · have h := rhF_fix_mono (zero_le : (0 : Ordinal.{0}) ≤ l) hf; rwa [rhF_zero] at h
  · obtain ⟨hnf, -, -⟩ := tl_nf hA.1 hA.2 heX
    have hle : tlLev e ≤ l := csInf_le' (show rhF l e ≠ e from hPe)
    have hf' : rhF (tlLev e) f = f := rhF_fix_mono hle hf
    have h : rhF (tlLev e) f < rhF (tlLev e) (tlI (tlLev e) e) := by rw [hf', hnf]; exact hfe
    exact ((rhF_lt _).1 h).le
  · obtain ⟨f, hf, hOf, hfy⟩ := hF; exact ⟨f, hf, hOf, hfy.le⟩

/-! ## The parts of a fixed point keep its gate -/

section Parts

variable {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (heX : e < tlX)
include hA hi heX

/-- The gate of a fixed point `F_λ(y)`. -/
theorem vs_fix_QE : yrQE e = max (yrQ (tlLev e)) (yrQ (tlI (tlLev e) e - glY0 (tlLev e))) := by
  obtain ⟨-, hlc, hyc, -, -⟩ := vs_fix_data hA hi heX
  exact yrQE_atom_fixL hA hi ⟨hlc, hyc⟩

/-- **The level keeps the gate.** -/
theorem vs_fix_gate_l : yrG (tlLev e) ≤ max ω (yrQE e) := by
  rw [vs_fix_QE hA hi heX]
  refine (le_max_right ω (yrG (tlLev e))).trans ?_
  rw [va_maxQ le_rfl (tlLev e)]
  exact max_le_max le_rfl (le_max_left _ _)

/-- **Past the largest fixed point `f < y` of `F_λ`: `f` and `y − (f+1)` keep the gate.** -/
theorem vs_fix_gate_f (hF : VaFixL (tlLev e) (tlI (tlLev e) e)) :
    yrG (vaFpL (tlLev e) (tlI (tlLev e) e)) ≤ max ω (yrQE e) ∧
      yrG (tlI (tlLev e) e - (vaFpL (tlLev e) (tlI (tlLev e) e) + 1)) ≤ max ω (yrQE e) := by
  obtain ⟨-, -, hyc, -, hne⟩ := vs_fix_data hA hi heX
  obtain ⟨hff, hOf, hfy⟩ := vs_fpL_mem hne hF
  have hfG : gamma (vaFpL (tlLev e) (tlI (tlLev e) e)) = vaFpL (tlLev e) (tlI (tlLev e) e) := by
    have h := rhF_fix_mono (zero_le : (0 : Ordinal.{0}) ≤ tlLev e) hff; rwa [rhF_zero] at h
  have hfSC : SC (vaFpL (tlLev e) (tlI (tlLev e) e)) := by rw [← hfG]; exact Lq.lq_gamma_SC _
  have hfE : InE (vaFpL (tlLev e) (tlI (tlLev e) e)) := Low.opow_eq_self_of_SC hfSC
  have hGf : gcG 0 ≤ vaFpL (tlLev e) (tlI (tlLev e) e) := gl_G0_le hfSC hOf
  have hsub : tlI (tlLev e) e - glY0 (tlLev e) = tlI (tlLev e) e :=
    Ordinal.sub_eq_of_add_eq (gl_absorb_le hfE hOf hfy.le)
  have hy : max ω (yrG (tlI (tlLev e) e)) ≤ max ω (yrQE e) := by
    rw [vs_fix_QE hA hi heX, hsub, va_maxQ le_rfl (tlI (tlLev e) e)]
    exact max_le_max le_rfl (le_max_right _ _)
  exact ⟨(vs_fpL_gate hne (hyc.trans heX) hF).trans hy, (vs_off_gate hfE hGf hfy).trans hy⟩

/-- **Below the first fixed point of `F_λ`: `y − y₀(λ)` keeps the gate.** -/
theorem vs_fix_gate_0 : yrG (tlI (tlLev e) e - glY0 (tlLev e)) ≤ max ω (yrQE e) := by
  rw [vs_fix_QE hA hi heX]
  refine (le_max_right ω (yrG (tlI (tlLev e) e - glY0 (tlLev e)))).trans ?_
  rw [va_maxQ le_rfl]
  exact max_le_max le_rfl (le_max_right _ _)

end Parts

end Googology.Trans.PoR.InaccPsi.R2.Va
