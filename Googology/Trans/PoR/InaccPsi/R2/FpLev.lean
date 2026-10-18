import Googology.Trans.PoR.InaccPsi.R2.LtP
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# The level `ω`: `ϑʸ(Ω₁·ω + η) = φ(ω, y + 1 + η)`, the readings of the `Lt`/`Ln` tops, and `GgPoly` from a reference

For a strongly critical base `y < Ω₁` (`ϑʸ = vt y`, `T^y = Tset y`, `P(y) = ltP y = sup_K c_K(y)`):

* `fpW_eq` (**`ϑʸ(Ω₁·ω + η) = φ(ω, y + 1 + η)` for `η ∈ T^y ∩ Ω₁`, `η < P(y)`**: `≤` by `Lt.lt_w_min` (no
  fixed point of `φ_ω` lies in `(y, P(y))`, `Lt.ltP_le_fix`), `≥` since `ϑʸ(Ω₁·ω + ·)` is strictly increasing below
  `P(y)` (`Lt.ltn_mono`) with values in the range of `φ_ω` (`Lt.lt_w_omega`));
* the readings of the tops (`Θ_y = Gg.ggTh y`): `fpTh_Yw` (`Θ_y(φ(ω, Ω₁ + ω)) = y_ω(y)`), `fpTh_T`
  (`Θ_y(φ(ω, phW K)) = T_K(y)`), `fpTh_Tw` (`Θ_y(φ(ω, φ(ω, Ω₁ + ω))) = sup_K T_K(y)`), `fpTh_C`
  (`Θ_y(fpCc K) = c_K(y)`, `fpCc 0 = φ(ω, Ω₁ + ω)`, `fpCc (K+1) = φ(ω, fpCc K)`), `fpTh_P`
  (**`Θ_y(φ(ω+1, Ω₁ + 1)) = P(y)`**, `fpP_eq`: `P(y) = φ(ω+1, y + 1)`);
* `fp_lt_Yw` (a code below `φ(ω, Ω₁ + ω)` lies below some `phW K`), `fp_lt_C` (an ordinal below
  `φ(ω+1, Ω₁ + 1)` lies below some `fpCc K`);
* `fpRef` (**above every `Z < Ω₁` there is a strongly critical `υ`-point `ρ < Ω₁`**: the supremum of
  `z₀ = Z`, `z_{n+1} = υ(φ(z_n, z_n) + 1)`), `fpPoly_of_R` (**`Ph.PhPolyR X E → Gg.GgPoly X E`**), `fpPoly_iff`,
  `fpPoly_lyEB` (**`GgPoly lyEB phEB`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Lz Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Ph

variable {Z : Ordinal.{0}}

theorem fp_prin {e : Ordinal.{0}} (he : InE e) : IsPrincipal (· + ·) e := by
  have := isPrincipal_add_omega0_opow e; unfold InE at he; rwa [he] at this

theorem fp_absorb {a e : Ordinal.{0}} (he : InE e) (ha : a < e) : a + e = e := by
  unfold InE at he; rw [← he] at ha ⊢; exact add_omega0_opow ha

/-- `y + 1 + e = e` for an `ε`-number `e > y`. -/
theorem fp_absorb1 {y e : Ordinal.{0}} (he : InE e) (hye : y < e) : y + 1 + e = e :=
  fp_absorb he (fp_prin he hye (one_lt_omega0.trans (omega0_lt_inE he)))

/-! ## The level `ω` -/

/-- **`ϑʸ(Ω₁·ω + η) = φ(ω, y + 1 + η)`** for `η ∈ T^y ∩ Ω₁` below `P(y)`. -/
theorem fpW_eq {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) :
    ∀ η, η ∈ Tset y → η < Om1 → η < ltP y → vt y (Om1 * ω + η) = veblen ω (y + 1 + η) := by
  have hyE : InE y := gg_SC_eps hy
  have hyw : veblen ω y = y := hy.veblen_right (ph_omega_lt hy)
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hηT hη1 hηP
  obtain ⟨K, hK⟩ := ltP_lt_iff.1 hηP
  have hne : η < veblen ω (y + 1 + η) := by
    by_contra hle
    push Not at hle
    have h1 : η ≤ y + 1 + η := le_add_self
    have h2 := right_le_veblen ω (y + 1 + η)
    have e1 : veblen ω (y + 1 + η) = η := le_antisymm hle (h1.trans h2)
    have e2 : y + 1 + η = η := le_antisymm (h2.trans e1.le) h1
    have hyη : y < η := by
      have h3 : y < y + 1 + η := (lt_add_one y).trans_le le_self_add
      rwa [e2] at h3
    rw [e2] at e1
    exact absurd (ltP_le_fix hyE hy1 e1 hyη) (not_le.2 hηP)
  apply le_antisymm
  · refine lt_w_min hyE hy1 hηT hη1 ⟨_, rfl⟩
      ((lt_add_one y).trans_le (le_self_add.trans (right_le_veblen _ _))) hne (fun σ hσ => ?_)
    have hσT : σ ∈ Tset y := vz_T_down hyE hy1 hηT hη1 hσ.le
    rw [IH σ hσ hσT (hσ.trans hη1) (hσ.trans hηP)]
    exact veblen_lt_veblen_iff_right.2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨δ, hδ⟩ := lt_w_omega hyE hy1 hηT hη1
    rw [← hδ]
    refine veblen_le_veblen_iff_right.2 ?_
    by_contra hlt
    push Not at hlt
    have hyv : y < veblen ω δ := by rw [hδ]; exact (lt_w_facts hyE hy1 hηT hη1).2.1
    have hyδ : y < δ := by
      by_contra hle
      push Not at hle
      have h4 := (veblen_le_veblen_iff_right (o := ω)).2 hle
      rw [hyw] at h4
      exact absurd hyv (not_lt.2 h4)
    obtain ⟨s, hs⟩ := exists_add_of_le (Order.add_one_le_of_lt hyδ)
    rw [hs] at hlt hδ
    have hsη : s < η := (add_lt_add_iff_left _).1 hlt
    have hsT : s ∈ Tset y := vz_T_down hyE hy1 hηT hη1 hsη.le
    have e := IH s hsη hsT (hsη.trans hη1) (hsη.trans hηP)
    have hm := ltn_mono hyE hy1 hsT hηT hη1 hK hsη
    rw [e, ← hδ] at hm
    exact lt_irrefl _ hm

/-! ## The readings of the tops -/

theorem fp_Om1' {y : Ordinal.{0}} (hy1 : y < Om 1) : y < Om1 := by rw [ph_Om1_eq]; exact hy1

section Read

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1)
include hy hy1

theorem fpTh_Om1w : ggTh y (Om 1 + ω) = y + ω := by
  rw [ggTh_add hy GgCl.om, ggTh_Om1 hy hy1, ggTh_small (ph_omega_lt hy).le]

/-- `y_ω(y) = φ(ω, y + ω)`. -/
theorem fpYw_eq : lzYw y = veblen ω (y + ω) := by
  have hyE : InE y := gg_SC_eps hy
  have h1 := fp_Om1' hy1
  have hωP : (ω : Ordinal.{0}) < ltP y :=
    (omega0_lt_inE (ltYw_E hyE h1)).trans (ltC_lt_P hyE h1 0)
  rw [ltYw_eq hyE h1, fpW_eq hy h1 ω (lt_omega_T hyE h1).1 (lt_omega_T hyE h1).2 hωP, add_assoc,
    one_add_omega0]

end Read

theorem fp_cl_Yw (hZ : SC Z) : GgCl Z phYw :=
  GgCl.phi (GgCl.small (ph_omega_lt hZ)) (GgCl.add GgCl.om (GgCl.small (ph_omega_lt hZ)))

theorem fpTh_Yw {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y phYw = lzYw y := by
  unfold phYw
  rw [phTh_veblen_omega hy (GgCl.add GgCl.om (GgCl.small (ph_omega_lt hy))), fpTh_Om1w hy hy1, fpYw_eq hy hy1]

/-- The code `φ(ω, phW K)` of `T_K`. -/
noncomputable def fpTc (K : ℕ) : Ordinal.{0} := veblen ω (phW K)

/-- The code `φ(ω, φ(ω, Ω₁ + ω))` of `sup_K T_K`. -/
noncomputable def fpTw : Ordinal.{0} := veblen ω phYw

/-- The codes of `c_K`: `fpCc 0 = φ(ω, Ω₁ + ω)`, `fpCc (K+1) = φ(ω, fpCc K)`. -/
noncomputable def fpCc : ℕ → Ordinal.{0}
  | 0 => phYw
  | K + 1 => veblen ω (fpCc K)

/-- The code `φ(ω+1, Ω₁ + 1)` of `P = sup_K c_K`. -/
noncomputable def fpPc : Ordinal.{0} := veblen (ω + 1) (Om 1 + 1)

theorem fp_w1_lt (hZ : SC Z) : ω + 1 < Z :=
  fp_prin (gg_SC_eps hZ) (ph_omega_lt hZ) (gg_one_lt_of_SC hZ)

theorem fp_cl_Tc (hZ : SC Z) (K : ℕ) : GgCl Z (fpTc K) := GgCl.phi (GgCl.small (ph_omega_lt hZ)) (ph_cl_W hZ K)

theorem fp_cl_Tw (hZ : SC Z) : GgCl Z fpTw := GgCl.phi (GgCl.small (ph_omega_lt hZ)) (fp_cl_Yw hZ)

theorem fp_cl_C (hZ : SC Z) : ∀ K, GgCl Z (fpCc K)
  | 0 => fp_cl_Yw hZ
  | K + 1 => GgCl.phi (GgCl.small (ph_omega_lt hZ)) (fp_cl_C hZ K)

theorem fp_cl_P (hZ : SC Z) : GgCl Z fpPc := GgCl.phi (GgCl.small (fp_w1_lt hZ)) (ph_cl_Om1_one hZ)

section Read2

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1)
include hy hy1

/-- `T_K(y) = φ(ω, y_K(y))`. -/
theorem fpT_eq (K : ℕ) : ltT y K = veblen ω (lzY y K) := by
  have hyE : InE y := gg_SC_eps hy
  have h1 := fp_Om1' hy1
  have hP : lzY y K < ltP y := (lzY_lt_w hyE h1 K).trans (ltC_lt_P hyE h1 0)
  unfold ltT
  rw [fpW_eq hy h1 _ (lzY_T hyE h1 K).1 (lzY_T hyE h1 K).2 hP,
    fp_absorb1 (lzY_facts hyE h1 K).2.2.2.1 (lzY_facts hyE h1 K).2.1]

/-- **`Θ_y(φ(ω, phW K)) = T_K(y)`.** -/
theorem fpTh_T (K : ℕ) : ggTh y (fpTc K) = ltT y K := by
  unfold fpTc
  rw [phTh_veblen_omega hy (ph_cl_W hy K), phTh_W hy hy1 K, fpT_eq hy hy1 K]

/-- `sup_K T_K(y) = φ(ω, y_ω(y))`. -/
theorem fpTw_eq : ltTw y = veblen ω (lzYw y) := by
  have hyE : InE y := gg_SC_eps hy
  have h1 := fp_Om1' hy1
  rw [ltTw_eq hyE h1, fpW_eq hy h1 _ (ltYw_T hyE h1).1 (ltYw_T hyE h1).2 (ltC_lt_P hyE h1 0),
    fp_absorb1 (ltYw_E hyE h1) ((lzY_facts hyE h1 0).2.1.trans_le (lzY_le_w y 0))]

/-- **`Θ_y(φ(ω, φ(ω, Ω₁ + ω))) = sup_K T_K(y)`.** -/
theorem fpTh_Tw : ggTh y fpTw = ltTw y := by
  unfold fpTw
  rw [phTh_veblen_omega hy (fp_cl_Yw hy), fpTh_Yw hy hy1, fpTw_eq hy hy1]

/-- `c_{K+1}(y) = φ(ω, c_K(y))`. -/
theorem fpC_succ_eq (K : ℕ) : ltC y (K + 1) = veblen ω (ltC y K) := by
  have hyE : InE y := gg_SC_eps hy
  have h1 := fp_Om1' hy1
  obtain ⟨hT, hc1, hyc, hcE⟩ := ltC_facts hyE h1 K
  rw [ltC_succ, fpW_eq hy h1 _ hT hc1 (ltC_lt_P hyE h1 K), fp_absorb1 hcE hyc]

/-- **`Θ_y(fpCc K) = c_K(y)`.** -/
theorem fpTh_C : ∀ K, ggTh y (fpCc K) = ltC y K
  | 0 => by show ggTh y phYw = lzYw y; exact fpTh_Yw hy hy1
  | K + 1 => by
    show ggTh y (veblen ω (fpCc K)) = _
    rw [phTh_veblen_omega hy (fp_cl_C hy K), fpTh_C K, fpC_succ_eq hy hy1 K]

end Read2

/-- The supremum of `f` with `f(K+1) = φ(ω, f(K))` is a fixed point of `φ_ω`. -/
theorem fp_sup_fix (f : ℕ → Ordinal.{0}) (hf : ∀ K, f (K + 1) = veblen ω (f K)) :
    veblen ω (⨆ K, f K) = ⨆ K, f K := by
  have e : ∀ K, f K = (veblen ω)^[K] (f 0) := by
    intro K
    induction K with
    | zero => rfl
    | succ K ih => rw [hf, ih, Function.iterate_succ_apply']
  have h : (⨆ K, f K) = nfp (veblen ω) (f 0) := by
    calc (⨆ K, f K) = ⨆ K, (veblen ω)^[K] (f 0) := iSup_congr e
      _ = nfp (veblen ω) (f 0) := iSup_iterate_eq_nfp _ _
  rw [h]
  exact nfp_fp (isNormal_veblen ω) _

/-- A fixed point `u > x` of `φ_ω` above a strongly critical `x` is at least `φ(ω+1, x + 1)`. -/
theorem fp_fix_ge {x u : Ordinal.{0}} (hx : SC x) (hu : veblen ω u = u) (hxu : x < u) :
    veblen (ω + 1) (x + 1) ≤ u := by
  have h0 : (ω + 1 : Ordinal.{0}) ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_one ω)).ne'
  obtain ⟨β, hβ⟩ : u ∈ Set.range (veblen (ω + 1)) :=
    (mem_range_veblen h0).2 (fun b hb => veblen_eq_self_of_le (Order.lt_add_one_iff.1 hb) hu)
  rw [← hβ]
  refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
  by_contra hle
  push Not at hle
  have h := (veblen_le_veblen_iff_right (o := ω + 1)).2 hle
  rw [hβ, hx.veblen_right (fp_w1_lt hx)] at h
  exact absurd hxu (not_lt.2 h)

/-- **`P(y) = φ(ω+1, y + 1)`.** -/
theorem fpP_eq {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ltP y = veblen (ω + 1) (y + 1) := by
  have hyE : InE y := gg_SC_eps hy
  have h1 := fp_Om1' hy1
  have hfix : veblen ω (ltP y) = ltP y := fp_sup_fix (ltC y) (fpC_succ_eq hy hy1)
  have hyP : y < ltP y := (ltC_facts hyE h1 0).2.2.1.trans (ltC_lt_P hyE h1 0)
  exact le_antisymm (ltP_le_fix hyE h1 (veblen_veblen_of_lt (lt_add_one ω) _)
    ((lt_add_one y).trans_le (right_le_veblen _ _))) (fp_fix_ge hy hfix hyP)

/-- **`Θ_y(φ(ω+1, Ω₁ + 1)) = P(y)`.** -/
theorem fpTh_P {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y fpPc = ltP y := by
  unfold fpPc
  rw [phTh_phi hy _ (GgCl.small (fp_w1_lt hy)) _ (ph_cl_Om1_one hy), ggTh_small (fp_w1_lt hy).le,
    phTh_Om1_one hy hy1, fpP_eq hy hy1]

/-! ## Codes below the limit tops -/

/-- A code below `φ(ω, Ω₁ + ω)` lies below some `phW K = φ(ω, Ω₁ + 1 + K)`. -/
theorem fp_lt_Yw {c : Ordinal.{0}} (hc : c < phYw) : ∃ K : ℕ, c < phW K := by
  have hlim : IsSuccLimit (Om (1 : Ordinal.{0}) + ω) := isSuccLimit_add _ isSuccLimit_omega0
  obtain ⟨ζ, hζ, hcζ⟩ := ((isNormal_veblen ω).lt_iff_exists_lt hlim).1 hc
  have hK : ∃ K : ℕ, ζ < Om 1 + 1 + K := by
    rcases lt_or_ge ζ (Om 1) with h | h
    · exact ⟨0, by rw [Nat.cast_zero, add_zero]; exact h.trans (lt_add_one _)⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le h
      obtain ⟨n, rfl⟩ := lt_omega0.1 ((add_lt_add_iff_left _).1 hζ)
      refine ⟨n + 1, ?_⟩
      calc Om 1 + (n : Ordinal.{0}) < Om 1 + ((n : Ordinal.{0}) + 1) := (add_lt_add_iff_left _).2 (lt_add_one _)
        _ = Om 1 + ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ]
        _ ≤ Om 1 + 1 + ((n + 1 : ℕ) : Ordinal.{0}) := add_le_add_left le_self_add _
  obtain ⟨K, hK⟩ := hK
  exact ⟨K, hcζ.trans (veblen_lt_veblen_iff_right.2 hK)⟩

/-- An ordinal below `φ(ω+1, Ω₁ + 1)` lies below some `fpCc K`. -/
theorem fp_lt_C {c : Ordinal.{0}} (hc : c < fpPc) : ∃ K : ℕ, c < fpCc K := by
  have hs := fp_sup_fix fpCc (fun K => rfl)
  have hO : Om 1 < ⨆ K, fpCc K := by
    have h1 : Om (1 : Ordinal.{0}) < phYw :=
      (lt_add_of_pos_right _ omega0_pos).trans_le (right_le_veblen _ _)
    exact h1.trans_le (Ordinal.le_iSup fpCc 0)
  exact Ordinal.lt_iSup_iff.1 (hc.trans_le (fp_fix_ge ph_SC_Om1 hs hO))

/-! ## A strongly critical `υ`-point above every countable ordinal; `GgPoly` from `PhPolyR` -/

/-- `z₀ = Z`, `z_{n+1} = υ(φ(z_n, z_n) + 1)`. -/
noncomputable def fpSeq (Z : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Z
  | n + 1 => upsilon (veblen (fpSeq Z n) (fpSeq Z n) + 1)

/-- **Above every `Z < Ω₁` there is a strongly critical `υ`-point `ρ < Ω₁`.** -/
theorem fpRef (hZ : Z < Om 1) : ∃ ρ, UpsPt ρ ∧ SC ρ ∧ ρ < Om 1 ∧ Z ≤ ρ := by
  have hO := ph_SC_Om1
  have hOE : InE (Om (1 : Ordinal.{0})) := gg_SC_eps hO
  have hlt : ∀ n, fpSeq Z n < Om 1 := by
    intro n
    induction n with
    | zero => exact hZ
    | succ n ih =>
      have h1 : veblen (fpSeq Z n) (fpSeq Z n) + 1 < Om 1 :=
        fp_prin hOE (hO.2 _ ih _ ih) (gg_one_lt_of_SC hO)
      have h2 := ups_lt_Om1 _ (by rw [ph_Om1_eq]; exact h1)
      rw [ph_Om1_eq] at h2
      exact h2
  have hstep : ∀ n, fpSeq Z n < fpSeq Z (n + 1) ∧ UpsPt (fpSeq Z (n + 1)) := fun n =>
    ⟨(right_le_veblen _ _).trans_lt ((lt_add_one _).trans_le upsilon_normal.strictMono.le_apply),
      upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))⟩
  have hmono : StrictMono (fpSeq Z) := strictMono_nat_of_lt_succ fun n => (hstep n).1
  have hle : ∀ n, fpSeq Z n ≤ ⨆ n, fpSeq Z n := fun n => Ordinal.le_iSup _ n
  have hρ1 : (⨆ n, fpSeq Z n) < Om 1 := by
    have h : (⨆ n, fpSeq Z n) < Om1 := Ordinal.iSup_lt_omega_one (fun n => by have h3 := hlt n; rw [← ph_Om1_eq] at h3; exact h3)
    rw [ph_Om1_eq] at h
    exact h
  have hlt' : ∀ a, a < (⨆ n, fpSeq Z n) → ∃ n, a < fpSeq Z n := fun a ha => Ordinal.lt_iSup_iff.1 ha
  have hpos : 0 < ⨆ n, fpSeq Z n := lt_of_le_of_lt zero_le ((hstep 0).1.trans_le (hle 1))
  refine ⟨⨆ n, fpSeq Z n, upsPt_of_cofinal hpos fun c hc => ?_, ⟨hpos, fun a ha b hb => ?_⟩, hρ1, hle 0⟩
  · obtain ⟨n, hn⟩ := hlt' c hc
    exact ⟨_, hn.trans (hstep n).1, (hstep (n + 1)).1.trans_le (hle _), (hstep n).2⟩
  · obtain ⟨i, hi⟩ := hlt' a ha
    obtain ⟨j, hj⟩ := hlt' b hb
    have hai : a < fpSeq Z (max i j) := hi.trans_le (hmono.monotone (le_max_left _ _))
    have hbj : b < fpSeq Z (max i j) := hj.trans_le (hmono.monotone (le_max_right _ _))
    calc veblen a b ≤ veblen (fpSeq Z (max i j)) b := veblen_left_monotone b hai.le
      _ < veblen (fpSeq Z (max i j)) (fpSeq Z (max i j)) := veblen_lt_veblen_iff_right.2 hbj
      _ < fpSeq Z (max i j + 1) := by
          show _ < upsilon _
          exact (lt_add_one _).trans_le upsilon_normal.strictMono.le_apply
      _ ≤ _ := hle _

/-- **`PhPolyR X E` gives `GgPoly X E`.** -/
theorem fpPoly_of_R {X : XtSys} {E : Ordinal.{0}} (h : PhPolyR X E) : GgPoly X E := by
  intro Z c hc hcE
  by_cases hZ : Z < Om 1
  · exact h Z c hc hcE (fpRef hZ)
  · exact ⟨X.cst 0, fun y _ hy1 hZy => absurd (hZy.trans_lt hy1) hZ⟩

theorem fpPoly_iff {X : XtSys} {E : Ordinal.{0}} : GgPoly X E ↔ PhPolyR X E := ⟨phPolyR_of, fpPoly_of_R⟩

/-- **`GgPoly lyEB phEB`** (in full). -/
theorem fpPoly_lyEB : GgPoly lyEB phEB := fpPoly_of_R phPoly_lyEB

end Googology.Trans.PoR.InaccPsi.R2.Fp
