import Googology.Trans.PoR.InaccPsi.R2.VjTop
import Googology.Trans.PoR.InaccPsi.R2.UgB

/-!
# The data of `Tᵝ ∩ [Ω₁², Ω₂)`, `B_n B₂ = B₂`, the atom move below `B₂`, and the two statement names of the port

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `π = pi σ τ`, `K_q = Ul.UlK S 0 q` (the `K⁽⁰⁾`-closure; `x ∈ K_q ↔
d(x) < q` at a strongly critical `q`, `Ul.ul_vis`), `Hˡ_γ = Ul.ulH S 1 γ`, `X = Tl.tlX`, `B₂ = Uc.ucB`,
`θ = ConjT.th S`, `Ω₃ = Om (1 + 1 + 1)`:

* `vmDat_T` (**every `x ∈ Tᵝ ∩ [Ω₁·Ω₁, Ω₂)`, `β < c_{n+1}` a countable `ε`-number, lies in `K_{c_{n+1}}`**: from
  `R2.vdArg_dat` at the level `x / Ω₁`), `vm_B_B2` (**`B_n B₂ = B₂`**), `vm_X_lt_pi` (**`X < π ξ` for `ξ ∈ Tᵗ[σ]`,
  `ξ ≥ B₂`**), `vmMoveLow` (**the atom move `B_n(Hˡ_γ y) = Hˡ_{B_n γ}(B_n y)` on `[X, B₂)`**, from `Uf.ufB_code`);
* the statement names `VmPiLev` (**(a): `π z < Ω₂` at an atom `z ∈ Tᵗ[σ] ∩ [B₂, θ)`, and at its level `λ ≥ Ω₂`:
  `π λ < Ω₃` and `Se.SeComm` at `λ`**) and `VmAtomMove` (**(b): `B_n(Hˡ_γ y) = Hˡ_{B_n γ}(B_n y)` and `B_n γ < Ω₃` at
  the atoms of `[B₂, θ)`**); `vmMove` (**(b) gives the move on all of `[X, θ)`**).

No new axiom.  New definitions: the statement names `VmPiLev`, `VmAtomMove`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vm

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Vd
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tl

variable {S : InaccSeq.{0}}

theorem vm_c_SC (n : ℕ) : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _

theorem vm_c_le (n : ℕ) : Bc.bcC S (n + 1) ≤ Om 1 := by
  have h := Uf.uf_c_le (S := S) n; rwa [Uf.uf_Om1] at h

/-- `Ω₁ ≤ M`, `M < θ` and `x = Ω₁·M + η₀` for `x ∈ [Ω₁·Ω₁, θ)`. -/
theorem vm_split {x : Ordinal.{0}} (hlo : Om1 * Om1 ≤ x) (hθ : x < ConjT.th S) :
    Om1 ≤ x / Om1 ∧ x / Om1 < ConjT.th S ∧ Om1 * (x / Om1) + x % Om1 = x ∧ x % Om1 < Om1 := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  exact ⟨(Ordinal.mul_le_iff_le_div hO0).1 hlo,
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right x rj_Om1_pos)).trans_lt hθ,
    Ordinal.div_add_mod x Om1, Ordinal.mod_lt x hO0⟩

/-- `Ω₁·M ∈ K_q` for `M ∈ K_q`. -/
theorem vm_K_Om1mul {q M : Ordinal.{0}} (hq : SC q) (hM : UlK S 0 q M) : UlK S 0 q (Om1 * M) := by
  have h := Us.us_K_Wmul (S := S) (s := 0) (i := 0) omega0_pos hq UlK.one hM
  rwa [Vj.vj_O01, opow_one, ← rj_Om1] at h

/-- **Every `x ∈ Tᵝ ∩ [Ω₁·Ω₁, Ω₂)` lies in `K_{c_{n+1}}`** (`β < c_{n+1}` a countable `ε`-number): `x = Ω₁·M + η₀`
with `Ω₁ ≤ M < θ`; `R2.vdArg_dat` puts the datum of `M` in `Tᵝ`, hence below `c_{n+1}`, and `η₀ ∈ Tᵝ ∩ Ω₁`. -/
theorem vmDat_T {n : ℕ} {β x : Ordinal.{0}} (hβ : InE β) (hβc : β < Bc.bcC S (n + 1)) (hx : x ∈ Tset β)
    (hlo : Om1 * Om1 ≤ x) (hx2 : x < OmTwo) : UlK S 0 (Bc.bcC S (n + 1)) x := by
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hθ : x < ConjT.th S := uzTBound β hβ hβ1 x hx hx2
  obtain ⟨hM1, hMθ, hdec, hη0Ω⟩ := vm_split hlo hθ
  have hc := vm_c_SC (S := S) n
  have hc1 := vm_c_le (S := S) n
  have hdat : VdDatAll (· ∈ Tset β) (x / Om1) := vdArg_dat hβ hβ1 hM1 hη0Ω (by rw [hdec]; exact hx)
  have hMK : UlK S 0 (Bc.bcC S (n + 1)) (x / Om1) := by
    rw [← Vg.vg_code_iffK hc]
    rcases lt_or_ge (x / Om1) ucB with hMB | hMB
    · have hu : ucDat (x / Om1) ∈ Tset β := hdat.1 hMB
      have hlt : ucDat (x / Om1) < Bc.bcC S (n + 1) := Si.si_T_lt_c hβ hβc hu (ucDat_lt_Om1 _)
      exact (vd_dat_uc hMB hc (by rw [rj_Om1]; exact hc1)).1 hlt
    · have hd : vdD S 0 (x / Om1) ∈ Tset β := hdat.2 S hMB hMθ
      have hd1 : vdD S 0 (x / Om1) < Om1 := lt_of_lt_of_eq (vdD_lt_Om1 hMθ) rj_Om1.symm
      exact Si.si_T_lt_c hβ hβc hd hd1
  have hη0T : x % Om1 ∈ Tset β := vzRem_T hβ hβ1 hx hx2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hη0c : x % Om1 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβ hβc hη0T hη0Ω
  rw [← hdec]
  exact UlK.add (vm_K_Om1mul hc hMK) (UlK.small hη0c)

/-- `MvD` from `K_{c_{n+1}}`. -/
theorem vm_D_of_K {n : ℕ} {x : Ordinal.{0}} (hx : UlK S 0 (Bc.bcC S (n + 1)) x) : Mv.MvD S x :=
  (Vj.vjD_lev (vm_c_SC n) (Bc.bcC_lt S (n + 1)).le ((ul_vis (vm_c_SC n)).2 hx)).2.2

/-- `B_n x < θ` from `x < θ`, `x ∈ K_{c_{n+1}}`. -/
theorem vm_B_lt_th {n : ℕ} {x : Ordinal.{0}} (hx : UlK S 0 (Bc.bcC S (n + 1)) x) (hθ : x < ConjT.th S) :
    Bc.bcB S n x < ConjT.th S :=
  (Vj.vj_B_lvl hθ ((ul_vis (vm_c_SC n)).2 hx)).2.1

/-- **`B_n B₂ = B₂`** (`B₂ = ψ_{Ω₂}(E₂)`, `B_n E₂ = E₂`). -/
theorem vm_B_B2 {n : ℕ} : Mv.MvD S ucB ∧ Bc.bcB S n ucB = ucB := by
  have hown : ucE ∈ S.CSet ucE (S.psi ucE (Om (1 + 1))) := uc_E_mem _ _
  obtain ⟨hDE, hBE⟩ := Uf.ufB_E (S := S) (n := n)
  obtain ⟨hD, hB, -⟩ := Ug.ugB_psi2 (S := S) (n := n) hDE hown
  rw [hBE, uc_psiE_eq_B] at hB
  rw [uc_psiE_eq_B] at hD
  exact ⟨hD, hB⟩

/-- `B₂ ≤ B_n x` for `x ≥ B₂` in the domain. -/
theorem vm_B2_le_B {n : ℕ} {x : Ordinal.{0}} (hD : Mv.MvD S x) (hx : ucB ≤ x) : ucB ≤ Bc.bcB S n x := by
  obtain ⟨hDB, hBB⟩ := vm_B_B2 (S := S) (n := n)
  refine not_lt.1 fun hlt => ?_
  rw [← hBB] at hlt
  exact absurd ((Mv.mvB_lt_iff hD hDB).1 hlt) (not_lt.2 hx)

theorem vm_OO_le_X : Om1 * Om1 ≤ (tlX : Ordinal.{0}) := by
  have h1 : Om1 * Om1 ≤ Om1 * ggE := mul_le_mul_right rj_Om1_lt_E.le _
  rw [Ss.ss_Om1_mul_E] at h1
  exact h1.trans (ggE_le_ggGam.trans Tz.tz_gg_lt_X.le)

theorem vm_E_le_B : (ggE : Ordinal.{0}) ≤ ucB := ggE_le_ggGam.trans (Tz.tz_gg_lt_X.trans uc_X_lt_B).le

/-- **`X < π ξ` for `ξ ∈ Tᵗ[σ]`, `ξ ≥ B₂`** (`X ∈ Tᵗ[σ]`, `π X = X`, `Uf.uf_pi_X`). -/
theorem vm_X_lt_pi {σ τ ξ : Ordinal.{0}} (h : Bases σ τ) (hξ : ξ ∈ TB τ σ) (hB : ucB ≤ ξ) :
    tlX < pi σ τ ξ := by
  obtain ⟨hXT, hπX⟩ := Uf.uf_pi_X ucCitPi uc_X_lt_B h
  have := (pi_bijOn h).2 hXT hξ (uc_X_lt_B.trans_le hB)
  rwa [hπX] at this

/-- **The atom move on `[X, B₂)`**: for `X ≤ Hˡ_γ(y) < B₂`, `γ < Ω₃`, `y < Hˡ_γ(y)`, `Hˡ_γ(y) ∈ K_{c_{n+1}}`:
`B_n γ < Ω₃` and `B_n(Hˡ_γ y) = Hˡ_{B_n γ}(B_n y)` (`Uf.ufB_code`, with `Hˡ_γ = H_γ` below `E₂`). -/
theorem vmMoveLow {n : ℕ} {γ y : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y)
    (hX : tlX ≤ ulH S 1 γ y) (hzB : ulH S 1 γ y < ucB) (hK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ y)) :
    Bc.bcB S n γ < Om (1 + 1 + 1) ∧ Bc.bcB S n (ulH S 1 γ y) = ulH S 1 (Bc.bcB S n γ) (Bc.bcB S n y) := by
  set z := ulH S 1 γ y with hz
  have hzS : SC z := ulH_SC γ y
  have h1 : Om 1 < z := ulH_gt γ y
  have h1' : Om1 < z := by rw [rj_Om1]; exact h1
  have hc := vm_c_SC (S := S) n
  have hc1 := vm_c_le (S := S) n
  obtain ⟨hlev, hidx⟩ := vdLev_H (S := S) hγ hy
  obtain ⟨hl, hi⟩ := vdLev_eq_uc (S := S) hzS h1 hzB
  rw [hlev] at hl hi
  rw [hidx] at hi
  have hne := uc_nf_of_lt hzS h1' hzB
  obtain ⟨hlE, -, -, -, -⟩ := ucLev_spec hzS h1' hne
  rw [← hl] at hlE
  have hdz : vdD S 0 z < Bc.bcC S (n + 1) := (Vg.vg_code_iffK hc).2 hK
  have hdu : ucDat z < Bc.bcC S (n + 1) := (vd_dat_uc hzB hc (by rw [rj_Om1]; exact hc1)).2 hdz
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := hc.1
  have hzcl : UcCl (Bc.bcC S (n + 1)) z := uc_code hc0 z hzB hdu
  obtain ⟨-, -, -, -, -, hlast⟩ := Uf.ufB_code (n := n) hc (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) z hzcl
  obtain ⟨-, hBz⟩ := hlast hzS hX
  rw [← hl] at hi hBz
  rw [← hi] at hBz
  have hW : z < Om (1 + 1) := hzB.trans (by rw [← Uf.uf_Om2]; exact ucB_lt_Om2)
  have hdγ : vdD S 0 γ < Bc.bcC S (n + 1) := ((vd_atom_dat hγ hy hW hc hc1).1 hdz).1
  have hDγ : Mv.MvD S γ := vm_D_of_K ((Vg.vg_code_iffK hc).1 hdγ)
  obtain ⟨hDE, hBE⟩ := Uf.ufB_E (S := S) (n := n)
  have hBγE : Bc.bcB S n γ < ucE := by
    have := (Mv.mvB_lt_iff (k := n) hDγ hDE).2 hlE; rwa [hBE] at this
  have e := (vd_lev_uc (S := S) hBγE hzS h1).1
  refine ⟨hBγE.trans vd_E_lt_V, ?_⟩
  rw [e]; exact hBz

/-! ## The two statement names -/

/-- **(a) The `π`-facts one cardinal up** (a hypothesis name): at every atom `z ∈ Tᵗ[σ] ∩ [B₂, θ)` with `z ∈
K_{c_{n+1}}` (every pair of bases of `Sv.SvUncAllFrom`): `π z < Ω₂`, and if its level `λ = vdLev S z` is `≥ Ω₂`, then
`π λ < Ω₃` and `Se.SeComm` holds at `λ`. -/
def VmPiLev (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ σ τ, Bases σ τ → Sp.SpLC σ → LtInf1 τ → Bc.bcC S n ≤ τ → τ < Bc.bcC S (n + 1) →
    ∀ z ∈ TB τ σ, SC z → ucB ≤ z → z < ConjT.th S → UlK S 0 (Bc.bcC S (n + 1)) z →
      pi σ τ z < OmTwo ∧ (OmTwo ≤ vdLev S z →
        pi σ τ (vdLev S z) < Om (1 + 1 + 1) ∧ Se.SeComm S n σ τ (vdLev S z))

/-- **(b) The atom move at `Ω₂` on `[B₂, θ)`** (a hypothesis name): `B_n γ < Ω₃` and `B_n(Hˡ_γ y) = Hˡ_{B_n γ}(B_n y)`
for every atom `B₂ ≤ Hˡ_γ(y) < θ` (`γ < Ω₃`, `y < Hˡ_γ(y)`) in `K_{c_{n+1}}`. -/
def VmAtomMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ γ y, γ < Om (1 + 1 + 1) → y < ulH S 1 γ y → ucB ≤ ulH S 1 γ y → ulH S 1 γ y < ConjT.th S →
    UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ y) →
      Bc.bcB S n γ < Om (1 + 1 + 1) ∧ Bc.bcB S n (ulH S 1 γ y) = ulH S 1 (Bc.bcB S n γ) (Bc.bcB S n y)

/-- **(b) gives the atom move on all of `[X, θ)`** (`vmMoveLow` below `B₂`). -/
theorem vmMove (hM : VmAtomMove S) {n : ℕ} {γ y : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y)
    (hX : tlX ≤ ulH S 1 γ y) (hθ : ulH S 1 γ y < ConjT.th S) (hK : UlK S 0 (Bc.bcC S (n + 1)) (ulH S 1 γ y)) :
    Bc.bcB S n γ < Om (1 + 1 + 1) ∧ Bc.bcB S n (ulH S 1 γ y) = ulH S 1 (Bc.bcB S n γ) (Bc.bcB S n y) := by
  rcases lt_or_ge (ulH S 1 γ y) ucB with hB | hB
  · exact vmMoveLow hγ hy hX hB hK
  · exact hM n γ y hγ hy hB hθ hK

end Googology.Trans.PoR.InaccPsi.R2.Vm
