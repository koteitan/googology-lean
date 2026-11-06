import Googology.Trans.PoR.InaccPsi.R2.QcGx
import Googology.Trans.PoR.InaccPsi.R2.VaFx

/-!
# QcFx: THE FIXED POINTS OF `Γ` FROM `X` ON AS CODES — THE LARGEST FIXED POINT OF `H_λ` BELOW THE INDEX

A fixed-point atom `e ∈ [X, B₂)` (`¬ yhJ e < e`) is `H_λ(y)` with `λ = ucLev e ≠ 0` (`H_0 = Γ`, `Qc.qc_H0`) and
`y = ucI λ e < e` not a fixed point of `H_λ` (`qc_fix_data`).  Its reading uses the largest fixed point `p < y` of
`H_λ` (`Qc.qcFpH`): `p` is a fixed point of `H_λ` (`qc_fpH_mem`), and **`p` is a code over every `Z ≤ Ω₁` over which `y`
is a code** (`qc_fpH_cl`): the largest fixed point of `H_λ` up to a code `c` is that up to a
part of `c` — a summand or a Veblen argument (it is strongly critical), the index or a component of the level at an
atom `H_μ(z)` that `H_λ` does not fix (`qc_key_H`: a fixed point `f < H_μ(z)` of `H_λ` has `f ≤ z` or `f` below a
component of `μ`), the index `y` at an atom `F_β(y)` below `X` (`qc_key_F`).

* `qc_fix_data`, `qc_fpH_closed`, `qc_fpH_eq`, `qc_fpH_mem`;
* `qc_key_H`, `qc_key_F`, `qc_mx_part`, `qc_mx_tl`, `qc_mx_cl`, `qc_fpH_cl` (**the largest fixed point is a code**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## Fixed-point atoms from `X` on -/

/-- **The data of a fixed-point atom `e ∈ [X, B₂)`**: `e = H_λ(y)`, `λ ≠ 0`, the components of `λ` below `e`,
`y < e` not a fixed point of `H_λ`. -/
theorem qc_fix_data {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : tlX ≤ e) (hB : e < ucB) :
    ucLev e ≠ 0 ∧ ucLev e < ucE ∧ ucC (ucLev e) < e ∧ ucI (ucLev e) e < e ∧
      ucH (ucLev e) (ucI (ucLev e) e) = e ∧ ucH (ucLev e) (ucI (ucLev e) e) ≠ ucI (ucLev e) e := by
  have hO : Om1 < e := tlX_gt.trans_le hX
  have hne := uc_nf_of_lt hA.1 hO hB
  obtain ⟨hl, hc, -, -, -⟩ := ucLev_spec hA.1 hO hne
  obtain ⟨hnf, hy⟩ := uc_nf hA.1 hO hne
  refine ⟨fun h0 => hi ?_, hl, hc, hy, hnf, by rw [hnf]; exact (ne_of_gt hy)⟩
  have hg : gcG (ucI (ucLev e) e) = e := by
    have h := hnf; rw [h0, qc_H0] at h
    rw [h0]; exact h
  rw [← hg, yhJ_gcG, hg]
  have := hy; rwa [h0] at this

/-! ## The largest fixed point of `H_λ` below the index -/

/-- The fixed points of `H_λ` above `Ω₁` are closed under suprema. -/
theorem qc_fpH_closed (l c : Ordinal.{0}) (hc : ∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ c) :
    ucH l (vsMx (fun f => ucH l f = f) c) = vsMx (fun f => ucH l f = f) c := by
  unfold vsMx
  show ucH l (sSup {f | ucH l f = f ∧ Om1 < f ∧ f ≤ c}) = sSup {f | ucH l f = f ∧ Om1 < f ∧ f ≤ c}
  rw [(ucH_normal l).map_sSup (s := {f | ucH l f = f ∧ Om1 < f ∧ f ≤ c}) hc ⟨c, fun _ h => h.2.2⟩]
  congr 1
  ext f
  constructor
  · rintro ⟨f', hf', rfl⟩
    have h1 : ucH l f' = f' := hf'.1
    rw [h1]; exact hf'
  · intro hf; exact ⟨f, hf, hf.1⟩

theorem qc_fpH_eq {l y : Ordinal.{0}} (hy : ucH l y ≠ y) : qcFpH l y = vsMx (fun f => ucH l f = f) y := by
  unfold qcFpH vsMx; congr 1; ext f
  refine ⟨fun h => ⟨h.1, ?_, h.2.le⟩, fun h => ⟨h.1, lt_of_le_of_ne h.2.2 fun e => hy (e ▸ h.1)⟩⟩
  rw [← h.1]; exact ucH_gt l f

/-- **The largest fixed point `p < y` of `H_λ`**: a fixed point of `H_λ` in `(Ω₁, y)`. -/
theorem qc_fpH_mem {l y : Ordinal.{0}} (hy : ucH l y ≠ y) (hF : QcFixH l y) :
    ucH l (qcFpH l y) = qcFpH l y ∧ Om1 < qcFpH l y ∧ qcFpH l y < y := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact ucH_gt l f
  have hex : ∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ y := ⟨f, hf, hOf, hfy.le⟩
  have hfix := qc_fpH_closed l y hex
  rw [qc_fpH_eq hy]
  refine ⟨hfix, hOf.trans_le (vs_mx_ge (fun f => ucH l f = f) hf hOf hfy.le), lt_of_le_of_ne (vs_mx_le (fun f => ucH l f = f) hex) fun e => hy ?_⟩
  rw [← e]; exact hfix

/-! ## The largest fixed point up to a code is that up to a part -/

/-- **A fixed point `f < H_μ(z)` of `H_λ` that does not fix `H_μ(z)`** has `f ≤ z` or `f` below a component of
`μ`. -/
theorem qc_key_H {l μ z f : Ordinal.{0}} (hc : ucH l (ucH μ z) ≠ ucH μ z) (hf : ucH l f = f)
    (hfc : f < ucH μ z) : f ≤ z ∨ ∃ d ∈ ucComps μ, f ≤ d := by
  rcases lt_or_ge l μ with hlμ | hμl
  · exfalso
    rcases lt_or_ge (ucC l) (ucH μ z) with hC | hC
    · exact hc (ucG_fix_lower hlμ ⟨z, rfl⟩ hC)
    · have h1 : ucC l < f := by rw [← hf]; exact ucH_C_lt l f
      exact absurd (h1.trans hfc) (not_lt.2 hC)
  · by_cases hC : ucC μ < f
    · have hfμ : ucH μ f = f := ucG_fix_mono hμl hf hC
      left
      by_contra hzf
      push Not at hzf
      have h1 : ucH μ z < ucH μ f := (ucH_lt_iff μ).2 hzf
      rw [hfμ] at h1
      exact absurd hfc (not_lt.2 h1.le)
    · right
      have hOf : Om1 < f := by rw [← hf]; exact ucH_gt l f
      have hf0 : 0 < f := Rj.rj_Om1_pos.trans hOf
      have h := (ucC_lt_iff hf0 μ).not.1 hC
      push Not at h
      exact h

/-- **A fixed point `f < F_β(y)` of `H_λ` (`F_β(y) < X` not fixed by `H_λ`, `β < F_β(y)`)** has `f ≤ y` or
`f ≤ β`. -/
theorem qc_key_F {l β y f : Ordinal.{0}} (hO : Om1 < rhF β y) (hX : rhF β y < tlX) (hβc : β < rhF β y)
    (hc : ucH l (rhF β y) ≠ rhF β y) (hf : ucH l f = f) (hfc : f < rhF β y) : f ≤ y ∨ f ≤ β := by
  have hβ2 : β < OmTwo := hβc.trans (hX.trans tlX_lt_OmTwo)
  obtain ⟨z, hz⟩ := (uc_range_F hβ2 (max_lt hO hβc)).2 ⟨y, rfl⟩
  have hzy : ucS β + z = y := by
    have h := hz; rw [ucH_eq_F hβ2 z] at h
    exact (rhF_normal β).strictMono.injective h
  rw [← hz] at hc hfc
  rcases qc_key_H hc hf hfc with h | ⟨d, hd, h⟩
  · left; exact h.trans (hzy ▸ le_add_self)
  · right; rw [ucComps_small hβ2, mem_singleton_iff] at hd; rw [← hd]; exact h

section Mx

variable {l : Ordinal.{0}}

/-- **The largest fixed point up to `c` is that up to a part `s ∈ [F, c]`.** -/
theorem qc_mx_part {c s : Ordinal.{0}} (hex : ∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ c) (hsc : s ≤ c)
    (hFs : vsMx (fun f => ucH l f = f) c ≤ s) :
    vsMx (fun f => ucH l f = f) s = vsMx (fun f => ucH l f = f) c ∧ ∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ s := by
  have hfix := qc_fpH_closed l c hex
  obtain ⟨f₀, hf₀, hO₀, h₀⟩ := hex
  have hOF : Om1 < vsMx (fun f => ucH l f = f) c := hO₀.trans_le (vs_mx_ge (fun f => ucH l f = f) hf₀ hO₀ h₀)
  exact ⟨vs_mx_eq (fun f => ucH l f = f) hsc fun f hf hOf hfc => (vs_mx_ge (fun f => ucH l f = f) hf hOf hfc).trans hFs, _, hfix, hOF, hFs⟩

/-- The largest fixed point is strongly critical. -/
theorem qc_mx_SC {c : Ordinal.{0}} (hex : ∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ c) :
    SC (vsMx (fun f => ucH l f = f) c) ∧ Om1 < vsMx (fun f => ucH l f = f) c ∧
      vsMx (fun f => ucH l f = f) c ≤ c := by
  have hfix := qc_fpH_closed l c hex
  obtain ⟨f₀, hf₀, hO₀, h₀⟩ := hex
  refine ⟨by rw [← hfix]; exact ucH_SC _ _, hO₀.trans_le (vs_mx_ge (fun f => ucH l f = f) hf₀ hO₀ h₀), vs_mx_le (fun f => ucH l f = f) ⟨f₀, hf₀, hO₀, h₀⟩⟩

variable {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1)
include hZ1

/-- **For a code of `TlCl Z` the largest fixed point of `H_λ` up to it is a code.** -/
theorem qc_mx_tl {c : Ordinal.{0}} (hc : TlCl Z c) :
    (∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ c) → UcCl Z (vsMx (fun f => ucH l f = f) c) := by
  induction hc with
  | @small x h =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qc_mx_SC hex
    exact absurd ((hle.trans_lt h).trans_le hZ1) (not_lt.2 hO.le)
  | om =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qc_mx_SC hex
    exact absurd hle (not_le.2 hO)
  | @add x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qc_mx_SC hex
    rcases le_or_gt (vsMx (fun f => ucH l f = f) (x + y)) x with h | h
    · obtain ⟨e, hex'⟩ := qc_mx_part hex le_self_add h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => ucH l f = f) (x + y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.isPrincipal h h2))
      obtain ⟨e, hex'⟩ := qc_mx_part hex le_add_self h2
      rw [← e]; exact ihy hex'
  | @phi x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qc_mx_SC hex
    rcases le_or_gt (vsMx (fun f => ucH l f = f) (veblen x y)) x with h | h
    · obtain ⟨e, hex'⟩ := qc_mx_part hex (left_le_veblen x y) h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => ucH l f = f) (veblen x y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.2 x h y h2))
      obtain ⟨e, hex'⟩ := qc_mx_part hex (right_le_veblen x y) h2
      rw [← e]; exact ihy hex'
  | @atom β y hβ hy h1 ihβ ihy =>
    intro hex
    have hfix := qc_fpH_closed l _ hex
    obtain ⟨-, -, hle⟩ := qc_mx_SC hex
    have hcX : rhF β y < tlX := uc_tl_lt_X hZ1 (TlCl.atom hβ hy h1)
    by_cases hP : ucH l (rhF β y) = rhF β y
    · have e : vsMx (fun f => ucH l f = f) (rhF β y) = rhF β y :=
        le_antisymm hle (vs_mx_ge (fun f => ucH l f = f) hP h1 le_rfl)
      rw [e]; exact UcCl.tl (TlCl.atom hβ hy h1)
    rcases (rhF_left_le β y).lt_or_eq with hβc | hβc
    · have hlt : vsMx (fun f => ucH l f = f) (rhF β y) < rhF β y :=
        lt_of_le_of_ne hle fun e => hP (by have h := hfix; rw [e] at h; exact h)
      rcases qc_key_F h1 hcX hβc hP hfix hlt with h | h
      · obtain ⟨e, hex'⟩ := qc_mx_part hex (rhF_le_self β y) h
        rw [← e]; exact ihy hex'
      · obtain ⟨e, hex'⟩ := qc_mx_part hex (rhF_left_le β y) h
        rw [← e]; exact ihβ hex'
    · rw [← hβc]; rw [← hβc] at hex; exact ihβ hex

/-- **For a code of `UcCl Z` the largest fixed point of `H_λ` up to it is a code.** -/
theorem qc_mx_cl {c : Ordinal.{0}} (hc : UcCl Z c) :
    (∃ f, ucH l f = f ∧ Om1 < f ∧ f ≤ c) → UcCl Z (vsMx (fun f => ucH l f = f) c) := by
  induction hc with
  | @small x h =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qc_mx_SC hex
    exact absurd ((hle.trans_lt h).trans_le hZ1) (not_lt.2 hO.le)
  | om =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qc_mx_SC hex
    exact absurd hle (not_le.2 hO)
  | @add x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qc_mx_SC hex
    rcases le_or_gt (vsMx (fun f => ucH l f = f) (x + y)) x with h | h
    · obtain ⟨e, hex'⟩ := qc_mx_part hex le_self_add h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => ucH l f = f) (x + y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.isPrincipal h h2))
      obtain ⟨e, hex'⟩ := qc_mx_part hex le_add_self h2
      rw [← e]; exact ihy hex'
  | @phi x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qc_mx_SC hex
    rcases le_or_gt (vsMx (fun f => ucH l f = f) (veblen x y)) x with h | h
    · obtain ⟨e, hex'⟩ := qc_mx_part hex (left_le_veblen x y) h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => ucH l f = f) (veblen x y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.2 x h y h2))
      obtain ⟨e, hex'⟩ := qc_mx_part hex (right_le_veblen x y) h2
      rw [← e]; exact ihy hex'
  | tl h => exact qc_mx_tl hZ1 h
  | @hatom γ y hγ hcomp hy hX ihc ihy =>
    intro hex
    have hfix := qc_fpH_closed l _ hex
    obtain ⟨-, -, hle⟩ := qc_mx_SC hex
    by_cases hP : ucH l (ucH γ y) = ucH γ y
    · have e : vsMx (fun f => ucH l f = f) (ucH γ y) = ucH γ y :=
        le_antisymm hle (vs_mx_ge (fun f => ucH l f = f) hP (ucH_gt γ y) le_rfl)
      rw [e]; exact UcCl.hatom hγ hcomp hy hX
    have hlt : vsMx (fun f => ucH l f = f) (ucH γ y) < ucH γ y :=
      lt_of_le_of_ne hle fun e => hP (by have h := hfix; rw [e] at h; exact h)
    rcases qc_key_H hP hfix hlt with h | ⟨d, hd, h⟩
    · obtain ⟨e, hex'⟩ := qc_mx_part hex (ucH_le_self γ y) h
      rw [← e]; exact ihy hex'
    · have hdc : d ≤ ucH γ y := (le_ucC hd).trans (ucH_C_lt γ y).le
      obtain ⟨e, hex'⟩ := qc_mx_part hex hdc h
      rw [← e]; exact ihc d hd hex'

/-- **The largest fixed point `p < y` of `H_λ` is a code** over every `Z ≤ Ω₁` over which `y` is one. -/
theorem qc_fpH_cl {y : Ordinal.{0}} (hy : UcCl Z y) (hne : ucH l y ≠ y) (hF : QcFixH l y) : UcCl Z (qcFpH l y) := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact ucH_gt l f
  rw [qc_fpH_eq hne]
  exact qc_mx_cl hZ1 hy ⟨f, hf, hOf, hfy.le⟩

end Mx

end Googology.Trans.PoR.InaccPsi.R2.Qc
