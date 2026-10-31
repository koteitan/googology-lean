import Googology.Trans.PoR.InaccPsi.R2.XdLift

/-!
# REFUTED: the candidate law `skX0Law` at the base `β = Ω_ω` (outside the domain of `T`)

`T = Vb.vbT S λ` is `0` off its domain `D` (`x < Ω_ω`): `T Ω_ω = 0` (`xdT_OmW`), so the candidate image
`X̂⁰_0(Ω_ω) = ψ₂(T Ω_ω + Ω₂) = Y₂ = ψ₂(Ω₂)`.  At the restart of `m* = L(0)` (`A = A_{η} > Ω_ω + Ω₃`) the base `Ω_ω`
satisfies `Ro.RoBaseE` at `Ω₃`, `Θ(ψ₂(Ω_ω)) = Θ(θ) = ψ₁(A + θ)` (`Wl.wlThVal`), and the lift at the base `Ω_ω`
(`Xd.xdLift`, `Â = A + θ`, `L(ζ) = Ω₂ + ζ`) gives `ψ₁(A + θ + z₂) ≤ Θ(ψ₂(Ω_ω + κ z₂)) ≤ Θ(ψ₂(Ω_ω + Ω₃))` with
`z₂ = ψ₂(Ω₂ + Y₂) > Y₂`; the law would give `Θ(ψ₂(Ω_ω + Ω₃)) = ψ₁(A + θ + Y₂) < ψ₁(A + θ + z₂)`.

* `xdT_OmW` (`T Ω_ω = 0`), `xdA_big` (`Ω_ω + Ω₃ < A` at the restart of `m*`), `xdBase_OmW` (`RoBaseE` at `β = Ω_ω`);
* `xdRef` (**a restart with an own `A` where `RoBaseE λ Ω₃ 0 Ω_ω` holds and the law with the image `X̂⁰_0(Ω_ω)`
  fails**), `xdX0Law_false` (**the statement of the skeleton node `skX0Law` is FALSE**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **`T Ω_ω = 0`**: `Ω_ω` is no value of the level shift. -/
theorem xdT_OmW {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    Vb.vbT S l (Om ω) = 0 := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  unfold Vb.vbT
  rw [dif_neg]
  rintro ⟨y, hy, e⟩
  obtain ⟨n, hn⟩ := rxOmW_nat hy.2.2
  have hn' : y < Om ((n : Ordinal.{0}) + 1) := hn.trans_le (Om_le_Om.2 le_self_add)
  have h := rxL_lt_lev hZ hZ1 hAt y hy n hn'
  change rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) y = Om ω at e
  rw [e] at h
  exact lt_irrefl _ (h.trans (Vb.vbOm_lt_W n))

/-- The restart of `m* = L(0)` with its own `A = A_η`. -/
theorem xdWit (S : InaccSeq.{0}) :
    ∃ l : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧
      upsilon l < Pv S (Om ω + Nc.ncPp S * 1) ∧
      ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) ∧
      S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := Vq.vqA_spec hl hX (n := 0) hn
  exact ⟨l, hl, e.symm, hX, hA, hρ⟩

/-- **`Ω_ω + Ω₃ < A`** at the restart of `m* = L(0)`. -/
theorem xdA_big {l : Ordinal.{0}} (e : upsilon l = Nc.ncL S 0)
    (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l) :
    Om ω + Om (1 + 1 + 1) < ConjT.Aη S (cdEta S l) := by
  by_contra hc
  push Not at hc
  have h1 : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) ≤ S.psi (Om ω + Om (1 + 1 + 1)) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one hc).1
  have h2 : S.psi (Om ω + Om (1 + 1 + 1)) (Om 1) < S.psi (Om ω + Om ω) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 Ry.ryOm3_lt)
      (CSet.add_mem (ConjT.OmW_mem S _ _) (Ry.ryOm3_mem _ _))
  have hθ0 : 0 < ConjT.th S := (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  have h3 : S.psi (Om ω + Om ω) (Om 1) ≤ upsilon l := by
    rw [e, Lw.lw_L_eq, mul_zero, add_zero]
    show S.psi (Om ω + Om ω) (Om 1) ≤ S.psi (ConjT.Aη S (Om ω)) (Om 1)
    unfold ConjT.Aη
    exact (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl (Ordinal.le_mul_right _ hθ0))).1
  rw [hρ] at h1
  exact lt_irrefl _ ((h1.trans_lt h2).trans_le h3)

/-- **`Ro.RoBaseE` at the base `Ω_ω`** (level `Ω₃`, exponent `0`) whenever `Ω_ω + Ω₃ < A`. -/
theorem xdBase_OmW {l : Ordinal.{0}} (hbig : Om ω + Om (1 + 1 + 1) < ConjT.Aη S (cdEta S l)) :
    Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 (Om ω) := by
  have hW3 : Le.leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  have hε : ω ^ Om ω = (Om ω : Ordinal.{0}) := gg_SC_eps Vb.vbOmW_SC
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hε3 : ω ^ Om (1 + 1 + 1) = (Om (1 + 1 + 1) : Ordinal.{0}) := gg_SC_eps (SC_Om h3)
  refine ⟨?_, ConjT.OmW_mem S _ _, by rw [hW3]; exact hbig, fun _ _ => ConjT.OmW_mem S _ _, ?_⟩
  · rw [hW3]
    refine ⟨Om ω, ?_⟩
    conv_rhs => rw [← hε3, ← hε]
    rw [← opow_add, Ordinal.add_absorp (by rw [hε]; exact Ry.ryOm3_lt) (by rw [hε]), hε]
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

/-- **REFUTATION**: at the restart of `m* = L(0)` the base `Ω_ω` satisfies `RoBaseE` and the law with the image
`X̂⁰_0(Ω_ω) = Y₂` fails. -/
theorem xdRef (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 (Om ω) ∧
      ¬ Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om ω)) 0 (Om ω) := by
  obtain ⟨l, hl, e, hX, hA, hρ⟩ := xdWit S
  have hbig := xdA_big e hρ
  refine ⟨l, _, _, hl, hX, hA, hρ, xdBase_OmW hbig, fun hlaw => ?_⟩
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set θ := ConjT.th S with hθdef
  have hWA : Om ω < A := lt_of_le_of_lt le_self_add hbig
  have hÂ : A + θ ∈ S.CSet (A + θ) (S.psi (A + θ) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA)
      (ConjT.th_mem S (hWA.trans_le le_self_add))
  have hb : gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω) (Om (1 + 1))) = S.psi (A + θ) (Om 1) :=
    Wl.wlThVal hl hX hA hρ
  have h := hlaw (A + θ) hÂ hb
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi hκ2 _
  have hX0 : Wv.wvX0 S l 0 (Om ω) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
    unfold Wv.wvX0; rw [xdT_OmW hl hX, zero_add, Nat.cast_zero, zero_add]
  rw [hX0, gxTh_zero] at h
  simp only [add_zero] at h
  rw [Ua.uaOe_fix (gg_SC_eps hY2SC) (psiS_bounds (S := S) _ 1).1] at h
  unfold Le.leTe at h
  rw [Vn.vnWe_Om3] at h
  -- the lift at the base `Ω_ω`
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hO : RxE S W (Om (1 + 1 : Ordinal.{0})) := by
    have h' := Wk.wkOm_E (S := S) (T := W) 2; rwa [Wz.wzTwo] at h'
  have hKO : κ (Om (1 + 1 : Ordinal.{0})) = Om (1 + 1 + 1) := by
    have h' := rxL_Om (S := S) (Z := upsilon l) (At := ldAtR S l) (T := W) (k := 2) (by norm_num)
    rwa [Wz.wzTwo] at h'
  have hX2 : S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) < Om (1 + 1) := psi_lt hκ2 _
  have hκ3 : ∀ ζ, RxE S W ζ → ζ < S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) → κ ζ < Om (1 + 1 + 1) :=
    fun ζ hζ hζX => by
      have h' := rxL_lt_lev hZ hZ1 hAt ζ hζ 1 (by rw [Nat.cast_one]; exact hζX.trans hX2)
      rwa [Nat.cast_one] at h'
  have hdvd : θ ∣ A + θ := by
    have := rxDvdTh (S := S) (cdEta S l) 1; rwa [mul_one] at this
  have hlift := xdLift hl hX (β := Om ω) (Â := A + θ) (Xb := S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)))
    (fun ζ => Om (1 + 1) + ζ) ⟨Om ω, ConjT.OmW_mem S _ _, hWA, rfl⟩ hb.symm.le hdvd Wz.wzX_lt_th.le
    (ConjT.OmW_mem S _ _)
    (fun ζ hζ hζX => lt_of_lt_of_le ((add_lt_add_iff_left _).2 (hκ3 ζ hζ hζX)) hbig.le)
    (fun _ _ _ => ConjT.OmW_mem S _ _)
    (fun ζ hζ hζX => ⟨Vh.vhE_add hO hζ, by
      have hk : κ (Om (1 + 1) + ζ) = κ (Om (1 + 1)) + κ ζ := Vh.vhK_add hl hX (Om (1 + 1)) hO ζ hζ
      show κ (Om (1 + 1) + ζ) ≤ Om ω + κ ζ
      rw [hk, hKO]
      exact add_le_add Ry.ryOm3_lt.le le_rfl,
      fun x hx => (Wz.wzLtPsi (hx.trans hζX)).trans_le (psi_mono hκ2 (add_le_add le_rfl hx.le)).1⟩)
  have hz2 := hlift (Wz.wzZ S 2) (Wz.wzZ_E 2) (Wz.wzZ_lt_X 2)
  have hmono : gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + κ (Wz.wzZ S 2)) (Om (1 + 1))) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om (1 + 1 + 1)) (Om (1 + 1))) :=
    gxTh_mono (psi_mono hκ2 (add_le_add le_rfl (hκ3 _ (Wz.wzZ_E 2) (Wz.wzZ_lt_X 2)).le)).1
  have hY : S.psi (Om (1 + 1)) (Om (1 + 1)) < Wz.wzZ S 2 := by
    have h1 := Wz.wzZ_lt (S := S) 1
    rwa [Wz.wzZ_succ, Wz.wzZ_zero, add_zero] at h1
  have hΩ2 : Om (1 + 1) < A + θ + Wz.wzZ S 2 :=
    ((vkOmW.2.trans hWA).trans_le le_self_add).trans_le le_self_add
  have hstrict : S.psi (A + θ + S.psi (Om (1 + 1)) (Om (1 + 1))) (Om 1) < S.psi (A + θ + Wz.wzZ S 2) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 hY)
      (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (Vq.vqY2_mem hΩ2))
  rw [h] at hmono
  exact lt_irrefl _ (hstrict.trans_le (hz2.trans hmono))

/-- **THE SKELETON STATEMENT `skX0Law` IS FALSE** (at `k = 0`, `β = Ω_ω`, the restart of `m*`). -/
theorem xdX0Law_false (S : InaccSeq.{0}) :
    ¬ ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β := by
  intro hall
  obtain ⟨l, ηx, A, hl, hX, hA, hρ, hB, hn⟩ := xdRef S
  have h := hall 0 l ηx A (Om ω) hl hX hA hρ
  simp only [Nat.cast_zero, zero_add] at h
  exact hn (h hB)

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdT_OmW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdA_big
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdBase_OmW
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdRef
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdX0Law_false
