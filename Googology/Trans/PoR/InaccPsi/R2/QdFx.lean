import Googology.Trans.PoR.InaccPsi.R2.QdSeg
import Googology.Trans.PoR.InaccPsi.R2.QcFx

/-!
# QdFx: THE FIXED POINTS OF `Γ` FROM `B₂` ON AS CODES — THE LARGEST FIXED POINT OF `Hᵛ_λ` BELOW THE INDEX

As `Qc.QcFx` with the Veblen levels.  A fixed-point atom `e ∈ [B₂, B₃)` (`¬ yhJ e < e`) is `Hᵛ_λ(y)` with `λ = qdLev e
≠ 0` (`Hᵛ_0 = H_0 = Γ` through `S`) and `y = qdI λ e < e` not a fixed point of `Hᵛ_λ` (`qd_fix_data`).  Its reading uses
the largest fixed point `p < y` of `Hᵛ_λ` (`Qd.qdFpH`): `p` is a fixed point of `Hᵛ_λ` (`qd_fpH_mem`), and **`p` is a
code over every `Z ≤ Ω₁` over which `y` is a code** (`qd_fpH_cl`): the largest fixed point of `Hᵛ_λ` up to a code `c`
is that up to a part of `c` — a summand or a Veblen argument, the index or a leaf of the level at a Veblen atom
`Hᵛ_μ(z)` that `Hᵛ_λ` does not fix (`qd_key_H`), the index or a component of the level at an atom `H_μ(z) = Hᵛ_μ(z)`
below `B₂` (`qd_key_uc`, with `Hᵛ_μ = H_μ` and the same visibility below `E₂` through `S`), the index `y` at an atom
`F_β(y)` below `X` (`qd_key_F`).

* `qd_uc_H`, `qd_uc_vis`, `qd_fix_data`, `qd_fpH_closed`, `qd_fpH_eq`, `qd_fpH_mem`;
* `qd_key_H`, `qd_key_uc`, `qd_key_F`, `qd_mx_part`, `qd_mx_SC`, `qd_mx_tl`, `qd_mx_uc`, `qd_mx_cl`, `qd_fpH_cl`
  (**the largest fixed point is a code**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **`Hᵛ_μ = H_μ` below `E₂`** (through `S`). -/
theorem qd_uc_H (S : InaccSeq.{0}) {μ : Ordinal.{0}} (hμ : μ < ucE) : qdH μ = ucH μ := by
  have h1 : Om 1 < ucB := by rw [← Rj.rj_Om1]; exact ucB_gt
  rw [qdH_eq_ul S (hμ.trans qd_E_lt_G2)]
  exact (Vd.vd_lev_uc (S := S) hμ ucB_SC h1).1

/-- **Below `E₂` the leaves of `μ` are below `v` iff its components are** (through `S`). -/
theorem qd_uc_vis (S : InaccSeq.{0}) {μ v : Ordinal.{0}} (hμ : μ < ucE) (hv : SC v) (h1 : Om1 < v) :
    qdFold id μ < v ↔ ucC μ < v := by
  have h1' : Om 1 < v := by rw [← Rj.rj_Om1]; exact h1
  rw [qd_vis (S := S) (hμ.trans qd_E_lt_G2) hv h1]
  exact (Vd.vd_lev_uc (S := S) hμ hv h1').2

/-! ## Fixed-point atoms from `B₂` on -/

/-- **The data of a fixed-point atom `e ∈ [B₂, B₃)`**: `e = Hᵛ_λ(y)`, `λ ≠ 0`, the leaves of `λ` below `e`, `y < e`
not a fixed point of `Hᵛ_λ`. -/
theorem qd_fix_data (S : InaccSeq.{0}) {e : Ordinal.{0}} (hA : YhAt e) (hi : ¬ yhJ e < e) (hX : ucB ≤ e)
    (hB : e < qdB) :
    qdLev e ≠ 0 ∧ qdLev e < qdG2 ∧ qdFold id (qdLev e) < e ∧ qdI (qdLev e) e < e ∧
      qdH (qdLev e) (qdI (qdLev e) e) = e ∧ qdH (qdLev e) (qdI (qdLev e) e) ≠ qdI (qdLev e) e := by
  have hO : Om1 < e := ucB_gt.trans_le hX
  have hne := qd_nf_of_lt hA.1 hO hB
  obtain ⟨hl, hc, -, -, -⟩ := qdLev_spec hA.1 hO hne
  obtain ⟨hnf, hy⟩ := qd_nf hA.1 hO hne
  refine ⟨fun h0 => hi ?_, hl, hc, hy, hnf, by rw [hnf]; exact (ne_of_gt hy)⟩
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  have hg : gcG (qdI (qdLev e) e) = e := by
    have h := hnf; rw [h0, qd_uc_H S h0E, qc_H0] at h
    rw [h0]; exact h
  rw [← hg, yhJ_gcG, hg]
  have := hy; rwa [h0] at this

/-! ## The largest fixed point of `Hᵛ_λ` below the index -/

/-- The fixed points of `Hᵛ_λ` above `Ω₁` are closed under suprema. -/
theorem qd_fpH_closed (l c : Ordinal.{0}) (hc : ∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) :
    qdH l (vsMx (fun f => qdH l f = f) c) = vsMx (fun f => qdH l f = f) c := by
  unfold vsMx
  show qdH l (sSup {f | qdH l f = f ∧ Om1 < f ∧ f ≤ c}) = sSup {f | qdH l f = f ∧ Om1 < f ∧ f ≤ c}
  rw [(qdH_normal l).map_sSup (s := {f | qdH l f = f ∧ Om1 < f ∧ f ≤ c}) hc ⟨c, fun _ h => h.2.2⟩]
  congr 1
  ext f
  constructor
  · rintro ⟨f', hf', rfl⟩
    have h1 : qdH l f' = f' := hf'.1
    rw [h1]; exact hf'
  · intro hf; exact ⟨f, hf, hf.1⟩

theorem qd_fpH_eq {l y : Ordinal.{0}} (hy : qdH l y ≠ y) : qdFpH l y = vsMx (fun f => qdH l f = f) y := by
  unfold qdFpH vsMx; congr 1; ext f
  refine ⟨fun h => ⟨h.1, ?_, h.2.le⟩, fun h => ⟨h.1, lt_of_le_of_ne h.2.2 fun e => hy (e ▸ h.1)⟩⟩
  rw [← h.1]; exact qdH_gt l f

/-- **The largest fixed point `p < y` of `Hᵛ_λ`**: a fixed point of `Hᵛ_λ` in `(Ω₁, y)`. -/
theorem qd_fpH_mem {l y : Ordinal.{0}} (hy : qdH l y ≠ y) (hF : QdFixH l y) :
    qdH l (qdFpH l y) = qdFpH l y ∧ Om1 < qdFpH l y ∧ qdFpH l y < y := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact qdH_gt l f
  have hex : ∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ y := ⟨f, hf, hOf, hfy.le⟩
  have hfix := qd_fpH_closed l y hex
  rw [qd_fpH_eq hy]
  refine ⟨hfix, hOf.trans_le (vs_mx_ge (fun f => qdH l f = f) hf hOf hfy.le),
    lt_of_le_of_ne (vs_mx_le (fun f => qdH l f = f) hex) fun e => hy ?_⟩
  rw [← e]; exact hfix

/-! ## The largest fixed point up to a code is that up to a part -/

/-- **A fixed point `f < Hᵛ_μ(z)` of `Hᵛ_λ` that does not fix `Hᵛ_μ(z)`** has `f ≤ z` or `f` below a leaf of `μ`. -/
theorem qd_key_H {l μ z f : Ordinal.{0}} (hc : qdH l (qdH μ z) ≠ qdH μ z) (hf : qdH l f = f)
    (hfc : f < qdH μ z) : f ≤ z ∨ ∃ d ∈ qdComps μ, f ≤ d := by
  rcases lt_or_ge l μ with hlμ | hμl
  · exfalso
    rcases lt_or_ge (qdFold id l) (qdH μ z) with hC | hC
    · exact hc (ucG_fix_lower hlμ ⟨z, rfl⟩ hC)
    · have h1 : qdFold id l < f := by rw [← hf]; exact qdH_D_lt l f
      exact absurd (h1.trans hfc) (not_lt.2 hC)
  · have hOf : Om1 < f := by rw [← hf]; exact qdH_gt l f
    have hf0 : 0 < f := Rj.rj_Om1_pos.trans hOf
    by_cases hC : qdFold id μ < f
    · have hfμ : qdH μ f = f := ucG_fix_mono hμl hf hC
      left
      by_contra hzf
      push Not at hzf
      have h1 : qdH μ z < qdH μ f := (qdH_lt_iff μ).2 hzf
      rw [hfμ] at h1
      exact absurd hfc (not_lt.2 h1.le)
    · right
      have h := (qdFold_lt_iff hf0 μ).not.1 hC
      unfold qdP at h
      push Not at h
      exact h

variable (S : InaccSeq.{0})
include S

/-- **A fixed point `f < H_μ(z)` of `Hᵛ_λ` (`μ < E₂`) that does not fix `H_μ(z)`** has `f ≤ z` or `f` below a
component of `μ`. -/
theorem qd_key_uc {l μ z f : Ordinal.{0}} (hμ : μ < ucE) (hc : qdH l (ucH μ z) ≠ ucH μ z) (hf : qdH l f = f)
    (hfc : f < ucH μ z) : f ≤ z ∨ ∃ d ∈ ucComps μ, f ≤ d := by
  rw [← qd_uc_H S hμ] at hc hfc
  rcases lt_or_ge l μ with hlμ | hμl
  · exfalso
    rcases lt_or_ge (qdFold id l) (qdH μ z) with hC | hC
    · exact hc (ucG_fix_lower hlμ ⟨z, rfl⟩ hC)
    · have h1 : qdFold id l < f := by rw [← hf]; exact qdH_D_lt l f
      exact absurd (h1.trans hfc) (not_lt.2 hC)
  · have hOf : Om1 < f := by rw [← hf]; exact qdH_gt l f
    have hf0 : 0 < f := Rj.rj_Om1_pos.trans hOf
    have hfS : SC f := by rw [← hf]; exact qdH_SC l f
    by_cases hC : ucC μ < f
    · have hfμ : qdH μ f = f := ucG_fix_mono hμl hf ((qd_uc_vis S hμ hfS hOf).2 hC)
      left
      by_contra hzf
      push Not at hzf
      have h1 : qdH μ z < qdH μ f := (qdH_lt_iff μ).2 hzf
      rw [hfμ] at h1
      exact absurd hfc (not_lt.2 h1.le)
    · right
      have h := (ucC_lt_iff hf0 μ).not.1 hC
      push Not at h
      exact h

/-- **A fixed point `f < F_β(y)` of `Hᵛ_λ` (`F_β(y) < X` not fixed by `Hᵛ_λ`, `β < F_β(y)`)** has `f ≤ y` or
`f ≤ β`. -/
theorem qd_key_F {l β y f : Ordinal.{0}} (hO : Om1 < rhF β y) (hX : rhF β y < tlX) (hβc : β < rhF β y)
    (hc : qdH l (rhF β y) ≠ rhF β y) (hf : qdH l f = f) (hfc : f < rhF β y) : f ≤ y ∨ f ≤ β := by
  have hβ2 : β < OmTwo := hβc.trans (hX.trans tlX_lt_OmTwo)
  have hβE : β < ucE := hβ2.trans ucE_gt
  obtain ⟨z, hz⟩ := (uc_range_F hβ2 (max_lt hO hβc)).2 ⟨y, rfl⟩
  have hzy : ucS β + z = y := by
    have h := hz; rw [ucH_eq_F hβ2 z] at h
    exact (rhF_normal β).strictMono.injective h
  rw [← hz] at hc hfc
  rcases qd_key_uc S hβE hc hf hfc with h | ⟨d, hd, h⟩
  · left; exact h.trans (hzy ▸ le_add_self)
  · right; rw [ucComps_small hβ2, mem_singleton_iff] at hd; rw [← hd]; exact h

section Mx

variable {l : Ordinal.{0}}

omit S in
/-- **The largest fixed point up to `c` is that up to a part `s ∈ [F, c]`.** -/
theorem qd_mx_part {c s : Ordinal.{0}} (hex : ∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) (hsc : s ≤ c)
    (hFs : vsMx (fun f => qdH l f = f) c ≤ s) :
    vsMx (fun f => qdH l f = f) s = vsMx (fun f => qdH l f = f) c ∧ ∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ s := by
  have hfix := qd_fpH_closed l c hex
  obtain ⟨f₀, hf₀, hO₀, h₀⟩ := hex
  have hOF : Om1 < vsMx (fun f => qdH l f = f) c :=
    hO₀.trans_le (vs_mx_ge (fun f => qdH l f = f) hf₀ hO₀ h₀)
  exact ⟨vs_mx_eq (fun f => qdH l f = f) hsc fun f hf hOf hfc =>
    (vs_mx_ge (fun f => qdH l f = f) hf hOf hfc).trans hFs, _, hfix, hOF, hFs⟩

omit S in
/-- The largest fixed point is strongly critical. -/
theorem qd_mx_SC {c : Ordinal.{0}} (hex : ∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) :
    SC (vsMx (fun f => qdH l f = f) c) ∧ Om1 < vsMx (fun f => qdH l f = f) c ∧
      vsMx (fun f => qdH l f = f) c ≤ c := by
  have hfix := qd_fpH_closed l c hex
  obtain ⟨f₀, hf₀, hO₀, h₀⟩ := hex
  refine ⟨by rw [← hfix]; exact qdH_SC _ _, hO₀.trans_le (vs_mx_ge (fun f => qdH l f = f) hf₀ hO₀ h₀),
    vs_mx_le (fun f => qdH l f = f) ⟨f₀, hf₀, hO₀, h₀⟩⟩

variable {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1)
include hZ1

/-- **For a code of `TlCl Z` the largest fixed point of `Hᵛ_λ` up to it is a code.** -/
theorem qd_mx_tl {c : Ordinal.{0}} (hc : TlCl Z c) :
    (∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) → QdCl Z (vsMx (fun f => qdH l f = f) c) := by
  induction hc with
  | @small x h =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qd_mx_SC hex
    exact absurd ((hle.trans_lt h).trans_le hZ1) (not_lt.2 hO.le)
  | om =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qd_mx_SC hex
    exact absurd hle (not_le.2 hO)
  | @add x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (x + y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex le_self_add h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (x + y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.isPrincipal h h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex le_add_self h2
      rw [← e]; exact ihy hex'
  | @phi x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (veblen x y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex (left_le_veblen x y) h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (veblen x y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.2 x h y h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex (right_le_veblen x y) h2
      rw [← e]; exact ihy hex'
  | @atom β y hβ hy h1 ihβ ihy =>
    intro hex
    have hfix := qd_fpH_closed l _ hex
    obtain ⟨-, -, hle⟩ := qd_mx_SC hex
    have hcX : rhF β y < tlX := uc_tl_lt_X hZ1 (TlCl.atom hβ hy h1)
    by_cases hP : qdH l (rhF β y) = rhF β y
    · have e : vsMx (fun f => qdH l f = f) (rhF β y) = rhF β y :=
        le_antisymm hle (vs_mx_ge (fun f => qdH l f = f) hP h1 le_rfl)
      rw [e]; exact QdCl.uc (UcCl.tl (TlCl.atom hβ hy h1))
    rcases (rhF_left_le β y).lt_or_eq with hβc | hβc
    · have hlt : vsMx (fun f => qdH l f = f) (rhF β y) < rhF β y :=
        lt_of_le_of_ne hle fun e => hP (by have h := hfix; rw [e] at h; exact h)
      rcases qd_key_F S h1 hcX hβc hP hfix hlt with h | h
      · obtain ⟨e, hex'⟩ := qd_mx_part hex (rhF_le_self β y) h
        rw [← e]; exact ihy hex'
      · obtain ⟨e, hex'⟩ := qd_mx_part hex (rhF_left_le β y) h
        rw [← e]; exact ihβ hex'
    · rw [← hβc]; rw [← hβc] at hex; exact ihβ hex

/-- **For a code of `UcCl Z` the largest fixed point of `Hᵛ_λ` up to it is a code.** -/
theorem qd_mx_uc {c : Ordinal.{0}} (hc : UcCl Z c) :
    (∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) → QdCl Z (vsMx (fun f => qdH l f = f) c) := by
  induction hc with
  | @small x h =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qd_mx_SC hex
    exact absurd ((hle.trans_lt h).trans_le hZ1) (not_lt.2 hO.le)
  | om =>
    intro hex
    obtain ⟨-, hO, hle⟩ := qd_mx_SC hex
    exact absurd hle (not_le.2 hO)
  | @add x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (x + y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex le_self_add h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (x + y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.isPrincipal h h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex le_add_self h2
      rw [← e]; exact ihy hex'
  | @phi x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (veblen x y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex (left_le_veblen x y) h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (veblen x y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.2 x h y h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex (right_le_veblen x y) h2
      rw [← e]; exact ihy hex'
  | tl h => exact qd_mx_tl S hZ1 h
  | @hatom γ y hγ hcomp hy hX ihc ihy =>
    intro hex
    have hfix := qd_fpH_closed l _ hex
    obtain ⟨-, -, hle⟩ := qd_mx_SC hex
    by_cases hP : qdH l (ucH γ y) = ucH γ y
    · have e : vsMx (fun f => qdH l f = f) (ucH γ y) = ucH γ y :=
        le_antisymm hle (vs_mx_ge (fun f => qdH l f = f) hP (ucH_gt γ y) le_rfl)
      rw [e]; exact QdCl.uc (UcCl.hatom hγ hcomp hy hX)
    have hlt : vsMx (fun f => qdH l f = f) (ucH γ y) < ucH γ y :=
      lt_of_le_of_ne hle fun e => hP (by have h := hfix; rw [e] at h; exact h)
    rcases qd_key_uc S hγ hP hfix hlt with h | ⟨d, hd, h⟩
    · obtain ⟨e, hex'⟩ := qd_mx_part hex (ucH_le_self γ y) h
      rw [← e]; exact ihy hex'
    · have hdc : d ≤ ucH γ y := (le_ucC hd).trans (ucH_C_lt γ y).le
      obtain ⟨e, hex'⟩ := qd_mx_part hex hdc h
      rw [← e]; exact ihc d hd hex'

/-- **For a code of `QdCl Z` the largest fixed point of `Hᵛ_λ` up to it is a code.** -/
theorem qd_mx_cl {c : Ordinal.{0}} (hc : QdCl Z c) :
    (∃ f, qdH l f = f ∧ Om1 < f ∧ f ≤ c) → QdCl Z (vsMx (fun f => qdH l f = f) c) := by
  induction hc with
  | uc h => exact qd_mx_uc S hZ1 h
  | @add x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (x + y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex le_self_add h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (x + y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.isPrincipal h h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex le_add_self h2
      rw [← e]; exact ihy hex'
  | @phi x y hx hy ihx ihy =>
    intro hex
    obtain ⟨hS, -, hle⟩ := qd_mx_SC hex
    rcases le_or_gt (vsMx (fun f => qdH l f = f) (veblen x y)) x with h | h
    · obtain ⟨e, hex'⟩ := qd_mx_part hex (left_le_veblen x y) h
      rw [← e]; exact ihx hex'
    · have h2 : vsMx (fun f => qdH l f = f) (veblen x y) ≤ y := by
        by_contra h2
        push Not at h2
        exact absurd hle (not_le.2 (hS.2 x h y h2))
      obtain ⟨e, hex'⟩ := qd_mx_part hex (right_le_veblen x y) h2
      rw [← e]; exact ihy hex'
  | @hatom γ y hγ hcomp hy hB ihc ihy =>
    intro hex
    have hfix := qd_fpH_closed l _ hex
    obtain ⟨-, -, hle⟩ := qd_mx_SC hex
    by_cases hP : qdH l (qdH γ y) = qdH γ y
    · have e : vsMx (fun f => qdH l f = f) (qdH γ y) = qdH γ y :=
        le_antisymm hle (vs_mx_ge (fun f => qdH l f = f) hP (qdH_gt γ y) le_rfl)
      rw [e]; exact QdCl.hatom hγ hcomp hy hB
    have hlt : vsMx (fun f => qdH l f = f) (qdH γ y) < qdH γ y :=
      lt_of_le_of_ne hle fun e => hP (by have h := hfix; rw [e] at h; exact h)
    rcases qd_key_H hP hfix hlt with h | ⟨d, hd, h⟩
    · obtain ⟨e, hex'⟩ := qd_mx_part hex (qdH_le_self γ y) h
      rw [← e]; exact ihy hex'
    · have hdc : d ≤ qdH γ y :=
        ((qdFold_lt_iff (lt_of_le_of_lt zero_le (qdH_D_lt γ y)) γ).1 (qdH_D_lt γ y) d hd).le
      obtain ⟨e, hex'⟩ := qd_mx_part hex hdc h
      rw [← e]; exact ihc d hd hex'

/-- **The largest fixed point `p < y` of `Hᵛ_λ` is a code** over every `Z ≤ Ω₁` over which `y` is one. -/
theorem qd_fpH_cl {y : Ordinal.{0}} (hy : QdCl Z y) (hne : qdH l y ≠ y) (hF : QdFixH l y) :
    QdCl Z (qdFpH l y) := by
  obtain ⟨f, hf, hfy⟩ := hF
  have hOf : Om1 < f := by rw [← hf]; exact qdH_gt l f
  rw [qd_fpH_eq hne]
  exact qd_mx_cl S hZ1 hy ⟨f, hf, hOf, hfy.le⟩

end Mx

end Googology.Trans.PoR.InaccPsi.R2.Qd
