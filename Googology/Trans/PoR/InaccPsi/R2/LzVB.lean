import Googology.Trans.PoR.InaccPsi.R2.LzVI

/-!
# `B₁(x) = B(B(x))`, and the IMG package of `B₁`

`B₁(x) = VzB1 x = sup_N ϑˣ(Ω₁·N + B(x) + 1)` (`R2.LzV`).  From the fixed-point levels of `R2.VzL` (no new axiom):

* `lz_th_lt_B` (`ϑˣ(Ω₁·n + σ) < B(x)` for `σ < B(x)`), `lz_th_B_lt` (**`ϑˣ(Ω₁·n + B(x)) < u`** for every value `u > B(x)`
  of `φ(ω, ·)`: minimality `vz_th_min`, and `ϑˣ(Ω₁·n + B(x)) ∉ P_{n+1}`);
* `lzB1_omega` (**`B₁(x)` is a value of `φ(ω, ·)`**), `lzB1_eq` (**`B₁(x) = B(B(x))`**, the least value of `φ(ω, ·)`
  above `B(x)`, `vzB_omega` at the base `B(x)`);
* `lzB1_lh` (**`lh(B₁(x)) = B₁(x)·ω`** in `R₁⁺`: `vz_lh_B` at the base `B(x)`, an `ε`-number below `Ω₁`), `lzWitB1`
  (**the witness pair of `B₁(ρ)`**: every covering copy has `B₁(f(ρ)) ≤ f(B₁(ρ))`; the copy of `B₁ ≤₁ B₁·ω` is a value
  of `φ(ω, ·)` above `f(B(ρ)) ≥ B(f(ρ))`, or a `υ`-point).

The IMG package of `B₁` needs no EXACT of `B₁` (it is only the top of a term system).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

section Facts

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `ϑˣ(Ω₁·n + σ) < B(x)` for `σ < B(x)`, `1 ≤ n`. -/
theorem lz_th_lt_B {n : ℕ} {σ : Ordinal.{0}} (hσ : σ < VzB x) :
    vt x (Om1 * (n : Ordinal.{0}) + σ) < VzB x := by
  have hB1 := xt_B_lt_Om1 hx hx1
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 (lz_BT hx hx1) hB1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hB1
  obtain ⟨N, hN⟩ := vzB_lt_iff.1 hσ
  set M := max N (n + 1) with hM
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hσM : σ < vt x (Om1 * (M : Ordinal.{0}) + 0) := hN.trans_le (vzN_le hx hx1 (le_max_left _ _))
  refine (vzVt_lt hx hx1 hσT hσ1 h0T (Ordinal.omega_pos 1) ?_ hσM).trans_le (vzN_le_B x M)
  rw [add_zero]
  calc Om1 * (n : Ordinal.{0}) + σ < Om1 * (n : Ordinal.{0}) + Om1 := (add_lt_add_iff_left _).2 hσ1
    _ = Om1 * ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
    _ ≤ Om1 * (M : Ordinal.{0}) := mul_le_mul_right (by exact_mod_cast le_max_right N (n + 1)) Om1

/-- **`ϑˣ(Ω₁·n + B(x)) < u`** for every value `u > B(x)` of `φ(ω, ·)`. -/
theorem lz_th_B_lt {n : ℕ} (hn : 1 ≤ n) {u : Ordinal.{0}} (hu : u ∈ Set.range (veblen ω)) (hBu : VzB x < u) :
    vt x (Om1 * (n : Ordinal.{0}) + VzB x) < u := by
  have hB1 := xt_B_lt_Om1 hx hx1
  have hxB := (vzB_omega hx hx1).2.1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hPu : VzP (k + 1) u := vz_omega_P hu k
  have hle := vz_th_min hx hx1 hn (lz_BT hx hx1) hB1 hPu (hxB.trans hBu) hBu
    (fun σ hσ => (lz_th_lt_B hx hx1 hσ).trans hBu)
  refine hle.lt_of_ne fun e => ?_
  have hnot := vz_th_notP hx hx1 hn (lz_BT hx hx1) hB1
  rw [e] at hnot
  exact hnot (vz_omega_P hu (k + 1))

/-- **`B₁(x)` is a value of `φ(ω, ·)`.** -/
theorem lzB1_omega : VzB1 x ∈ Set.range (veblen ω) := by
  obtain ⟨hηT, hη1⟩ := lz_B1T hx hx1
  have hfa : ∀ N : ℕ, 1 ≤ N → VzP N (vt x (Om1 * (N : Ordinal.{0}) + (VzB x + 1))) :=
    fun N hN => vz_th_P hx hx1 N hN _ hηT hη1
  have hB1pos : 0 < VzB1 x := (xt_B_E hx hx1).pos.trans (lz_B_lt_B1 hx hx1)
  refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
  obtain ⟨k, rfl⟩ := lt_omega0.1 hb
  refine le_antisymm ?_ (right_le_veblen _ _)
  have hlim : IsSuccLimit (VzB1 x) := by
    refine Ordinal.isSuccLimit_iff.2 ⟨hB1pos.ne', ?_⟩
    refine isSuccPrelimit_of_succ_lt (fun a ha => ?_)
    obtain ⟨N, hN⟩ := lzB1_lt_iff.1 ha
    have hN' := hN.trans_le (lz_vtN_le hx hx1 hηT hη1 (le_max_left N 1))
    have hE := vzP_E (le_max_right N 1) (hfa _ (le_max_right N 1))
    exact ((ev_isSuccLimit_of_inE hE).succ_lt hN').trans_le (lzN1_le_B1 x _)
  rw [(isNormal_veblen _).apply_of_isSuccLimit hlim]
  refine Ordinal.iSup_le (fun j => ?_)
  obtain ⟨N, hN⟩ := lzB1_lt_iff.1 j.2
  set N' := max N (k + 1) with hN'
  have hjN : j.1 < vt x (Om1 * (N' : Ordinal.{0}) + (VzB x + 1)) :=
    hN.trans_le (lz_vtN_le hx hx1 hηT hη1 (le_max_left _ _))
  have hP : VzP (k + 1) (vt x (Om1 * (N' : Ordinal.{0}) + (VzB x + 1))) :=
    vzP_mono (by omega) (le_max_right _ _) (hfa N' (by omega))
  have hfix := vzP_succ.1 hP
  refine (le_of_lt ?_).trans (lzN1_le_B1 x N')
  have := (veblen_lt_veblen_iff_right (o := (k : Ordinal.{0}))).2 hjN
  rwa [hfix] at this

/-- **`B₁(x) = B(B(x))`.** -/
theorem lzB1_eq : VzB1 x = VzB (VzB x) := by
  have hBE := xt_B_E hx hx1
  have hB1 := xt_B_lt_Om1 hx hx1
  obtain ⟨hBBω, hBBB, -⟩ := vzB_omega hBE hB1
  refine le_antisymm (Ordinal.iSup_le fun N => ?_)
    ((vzB_omega hBE hB1).2.2 _ (lzB1_omega hx hx1) (lz_B_lt_B1 hx hx1))
  obtain ⟨hηT, hη1⟩ := lz_B1T hx hx1
  refine (lz_vtN_le hx hx1 hηT hη1 (Nat.le_succ N)).trans ?_
  have hn : 1 ≤ N + 1 := Nat.succ_pos N
  have hBBE := vz_omega_E hBBω
  have hxBB := (vzB_omega hx hx1).2.1.trans hBBB
  refine vz_th_min hx hx1 hn hηT hη1 (vz_omega_P hBBω N) hxBB
    ((inE_indec hBBE).add_lt hBBB (one_lt_omega0.trans (omega0_lt_inE hBBE))) (fun σ hσ => ?_)
  have hσB : σ ≤ VzB x := Order.lt_add_one_iff.1 hσ
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 (lz_BT hx hx1) hB1 hσB
  exact (vz_th_le hx hx1 hn hσT (lz_BT hx hx1) hB1 hσB).trans_lt (lz_th_B_lt hx hx1 hn hBBω hBBB)

/-- **`lh(B₁(x)) = B₁(x)·ω`** in `R₁⁺`. -/
theorem lzB1_lh : IsLh1 (VzB1 x) (VzB1 x * ω) := by
  rw [lzB1_eq hx hx1]
  exact vz_lh_B (xt_B_E hx hx1) (xt_B_lt_Om1 hx hx1)

end Facts

namespace LzK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The witness pair of `B₁(ρ)`**: every covering copy `f` has `B₁(f(ρ)) ≤ f(B₁(ρ))`. -/
theorem lzWitB1 : ImgPkg ρ δ VzB1 := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set v := VzB1 ρ with hv
  have hvω := lzB1_omega hρE hρ1
  have hρB := (vzB_omega hρE hρ1).2.1
  have hBv : VzB ρ < v := lz_B_lt_B1 hρE hρ1
  have hρv : ρ < v := hρB.trans hBv
  have hvδ : v < δ := (lzB1_le_next hρE hρ1 h.ρτ h.τU.2).trans_lt h.τδ
  have hvE : InE v := vz_omega_E hvω
  have hvwδ : v * ω < δ := vz_mul_omega_lt h.δE hvδ
  have hvw : v ≤ v * ω := by
    calc v = v * 1 := (mul_one _).symm
      _ ≤ v * ω := mul_le_mul_right one_lt_omega0.le v
  have hsrc : le1 v (v * ω) := (h.lowδ _ _ hρv hvwδ.le).2 (lzB1_lh hρE hρ1).1
  have hwI : Indec (v * ω) := by
    have e : v * ω = ω ^ (v + 1) := by
      rw [opow_add, opow_one, show ω ^ v = v from hvE]
    rw [e]; exact indec_opow _
  obtain ⟨hwB, -, hIB⟩ := xtWitB h
  have w2 : WZ ρ δ (insert v {VzB ρ * ω, VzB ρ, ρ}) ∅ := hwB.insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w3 : WZ ρ δ (insert (v * ω) (insert v {VzB ρ * ω, VzB ρ, ρ})) ∅ :=
    w2.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  refine ⟨(one_le_iff_pos.2 h.ρU.1).trans hρv.le, hvδ, _, _, w3, by simp [hv], fun A f hW hZ C => ?_⟩
  have hvA : v ∈ A := hW (by simp)
  have hvwA : v * ω ∈ A := hW (by simp)
  have hWB : ↑({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) ⊆ A := fun x hx =>
    hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
  have hBA : VzB ρ ∈ A := hWB (by simp)
  obtain ⟨-, hfB⟩ := hIB A f hWB hZ C
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hBy := xt_B_E hfρE hfρ1
  have hBy1 := xt_B_lt_Om1 hfρE hfρ1
  have hfBv : f (VzB ρ) < f v := C.mono hBA hvA hBv
  have hByv : VzB (f ρ) < f v := hfB.trans_lt hfBv
  show VzB1 (f ρ) ≤ f v
  rw [lzB1_eq hfρE hfρ1]
  have hadd : f v + f (v * ω) = f (v * ω) :=
    C.add v hvA (v * ω) hvwA (v * ω) hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f v * ω ≤ f (v * ω) := add_eq_right_iff_mul_omega0_le.1 hadd
  have himg : le1 (f v) (f (v * ω)) := C.cov1 v hvA _ hvwA hsrc
  by_cases hU : UpsPt (f v)
  · exact vzB_le_next hBy hBy1 hByv hU.2
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have hfv0 : 0 < f v := lt_of_le_of_lt zero_le hByv
    have hfvw : f v ≤ f v * ω := by
      calc f v = f v * 1 := (mul_one _).symm
        _ ≤ f v * ω := mul_le_mul_right one_lt_omega0.le (f v)
    have hR' : le1R (f v) (f v * ω) := le1R_of_le hfvw hge hR
    exact (vzB_omega hBy hBy1).2.2 (f v) (vz_le1R_omega hfv0 hR') hByv

end LzK

end Googology.Trans.PoR.InaccPsi.R2.Lz
