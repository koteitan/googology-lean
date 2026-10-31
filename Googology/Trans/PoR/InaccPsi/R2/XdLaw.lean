import Googology.Trans.PoR.InaccPsi.R2.XdIt
import Googology.Trans.PoR.InaccPsi.R2.XdUp
import Googology.Trans.PoR.InaccPsi.R2.XdRef

/-!
# THE LAW AT `k = 0` FOR EVERY BASE `β` IN THE DOMAIN OF `T`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`),
`X̂⁰_0(β) = ψ₂(T β + Ω₂)` (`Wv.wvX0`), `κ` the level shift (`T⁻¹`).

For `β ∈ D` with `Ro.RoBaseE λ Ω₃ 0 β` (`Ω₃ ∣ β`, `β + Ω₃ < A`, `β` normal up to `β + Ω₃`):
* upper half: `Xd.xdUp_at` at `a = β + Ω₃` (`T(β + Ω₃) = T β + Ω₂`): `Θ(ψ₂(β + Ω₃)) ≤ ψ₁(A + X̂⁰_0(β))`;
* lower half: the lift `Xd.xdLift` at the base `β` with `Â = A` and the level bound `L(ζ) = T β + ζ`
  (`κ L(ζ) = β + κ ζ`; `x < ψ₂(T β + x)` below `ψ₂(T β + Ω₂)` by `Xd.xdLtPsi`, since `T β` is normal by the transfer
  and `T β ≡ 0 mod Ω₂`, `xdT_mod`), and the iterates over `T β` are cofinal (`Xd.xdX_le_sup`);
* the own image `Â_β` of `ψ₂(β)` lies in `[A, A + 1 + ψ₂(T β)]` (`Xd.xdUp_at` at `β`), so `Â_β + X̂ = A + X̂`.

* `xdModHead`, `xdT_mod` (`Ω₃ ∣ x ⇒ Ω₂ ∣ T x` on `D`), `xdT_leaf` (`T β ∈ Cl(a', b')` when `Ω_ω ≤ a'`,
  `Θ(ψ₂(β)) ≤ b'`), `xdLow0` (**the lower half**), `xdLaw0D` (**THE LAW AT `k = 0`, EVERY `β ∈ D`**),
  `xdBase_Om3`, `xdLaw0D_wit` (non-vacuity at the restart of `m*`, `β = Ω₃`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

theorem xdModHead {P π e s : Ordinal.{0}} (hP : ω ^ π = P) (h : π ≤ e) (n : ℕ) :
    (ω ^ e * n + s) % P = s % P := by
  rw [← Ordinal.add_sub_cancel_of_le h, opow_add, hP, mul_assoc, Ordinal.mul_add_mod_self]

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Ω₃ ∣ x ⇒ Ω₂ ∣ T x`** on the domain. -/
theorem xdT_mod : ∀ x, VbD S l x → x % Om (1 + 1 + 1) = 0 → vbT S l x % Om (1 + 1) = 0 := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h3ε : ω ^ Om (1 + 1 + 1) = (Om (1 + 1 + 1) : Ordinal.{0}) := gg_SC_eps (SC_Om h3)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hm
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Vh.vhT_zero hl hX, Ordinal.zero_mod]
  have hx3 : Om (1 + 1 + 1) ≤ x := by
    by_contra hc
    push Not at hc
    rw [Ordinal.mod_eq_of_lt hc] at hm
    exact hx0 hm
  have hx2 : Om (1 + 1) ≤ x := (Om_le_Om.2 le_self_add).trans hx3
  have hT2 : Om (1 + 1) ≤ vbT S l x := by
    have h := vbT_ge_lev hl hX hx 1 (by rw [Nat.cast_one]; exact hx3)
    rwa [Nat.cast_one] at h
  by_cases hε : ω ^ x = x
  · have he := vbT_eps hl hX hx hx2 hε
    rw [← he] at hT2 ⊢
    exact xdMod_opow hT2
  have hlog : log ω x < x := ruLog_lt ((Om_lt_Om.2 (lt_add_one 1)).trans_le hx2) hε
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hsx : x % ω ^ log ω x < x := hs.trans_le (opow_log_le_self ω hx0)
  have hxE := vbD_E hl hX hx
  obtain ⟨heD, -, -⟩ := vbD_log hx hxE
  obtain ⟨hsD, -, -⟩ := vbD_rem hx hxE
  have he3 : Om (1 + 1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [h3ε]; exact hx3)
  have e1 : (ω ^ log ω x * n + x % ω ^ log ω x) % Om (1 + 1 + 1) =
      (x % ω ^ log ω x) % Om (1 + 1 + 1) := xdModHead h3ε he3 n
  rw [← hdm, hm] at e1
  have hTs := IH _ hsx hsD e1.symm
  have hTe : Om (1 + 1) ≤ vbT S l (log ω x) := by
    have h := vbT_ge_lev hl hX heD 1 (by rw [Nat.cast_one]; exact he3)
    rwa [Nat.cast_one] at h
  rw [(congrArg (vbT S l) hdm).trans (Vh.vhT_cnf hl hX n hn1 heD hsD hs), xdModHead Ru.ruOm2_eps hTe n]
  exact hTs

/-- **The leaves of `T β` are below `Θ(ψ₂(β))`**: `T β ∈ Cl(a', b')` for `Ω_ω ≤ a'`, `Θ(ψ₂(β)) ≤ b'`. -/
theorem xdT_leaf {β a' b' : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (ha' : Om ω ≤ a') (hb' : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) ≤ b') :
    vbT S l β ∈ S.CSet a' b' := by
  refine xdT_cl hl hX (psi_lt (InR_Om_succ 1) β).le (fun e he _ => (vbT_mem hl hX he).2.trans_le ha')
    (fun c hc hc2 hcC => ?_) β hβD hβn
  rw [vbT_code hl hX hc2 hc.1]
  exact CSet.of_lt ((gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1)
    (lt_psi_of_mem (InR_Om_succ 1) hcC hc2)).trans_le hb')

/-- **THE LOWER HALF AT `k = 0`, EVERY BASE `β ∈ D`**: `ψ₁(A + ψ₂(T β + Ω₂)) ≤ Θ(ψ₂(β + Ω₃))`. -/
theorem xdLow0 {A β : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 β) :
    S.psi (A + S.psi (vbT S l β + Om (1 + 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om (1 + 1 + 1)) (Om (1 + 1))) := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set b := vbT S l β with hbdef
  set Xh := S.psi (b + Om (1 + 1)) (Om (1 + 1)) with hXhdef
  have hW3 : Le.leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  obtain ⟨hdvd3, -, hlt, hnorm, -⟩ := hB
  rw [hW3] at hdvd3 hlt hnorm
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hnorm 0 zero_le; rwa [add_zero] at h
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := xdTr hl hX hβD hβD hβn
  have hbm : b % Om (1 + 1) = 0 := xdT_mod hl hX β hβD (Ordinal.mod_eq_zero_of_dvd hdvd3)
  have hbW : b < Om ω := (vbT_mem hl hX hβD).2
  have hXSC : SC Xh := SC_psi hκ2 _
  have hθW : ConjT.th S < Om ω := (psi_lt hκ2 _).trans vkOmW.2
  have hθ : Xh < ConjT.th S :=
    psi_lt_psi_of_mem hκ2 (vkOmW.1.isPrincipal hbW vkOmW.2)
      (CSet.add_mem (vbT_mem hl hX hβD).1 (mxOm2_mem _ _))
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hX2 : Xh < Om (1 + 1) := psi_lt hκ2 _
  have hκ3 : ∀ ζ, RxE S W ζ → ζ < Xh → κ ζ < Om (1 + 1 + 1) := fun ζ hζ hζX => by
    have h' := rxL_lt_lev hZ hZ1 hAt ζ hζ 1 (by rw [Nat.cast_one]; exact hζX.trans hX2)
    rwa [Nat.cast_one] at h'
  obtain ⟨hbE, hbK⟩ := vbT_eq hl hX hβD
  have hdvd : ConjT.th S ∣ A := by
    have := rxDvdTh (S := S) (cdEta S l) 0; rwa [mul_zero, add_zero] at this
  have hβA : β < A := lt_of_le_of_lt le_self_add hlt
  have hbase : S.psi A (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) := by
    rw [hρ]
    exact (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) _ 1).1.le)
  have hlift := xdLift hl hX (β := β) (Â := A) (Xb := Xh) (fun ζ => b + ζ) ⟨β, hβD.1, hβA, rfl⟩ hbase hdvd
    hθ.le hβD.1
    (fun ζ hζ hζX => lt_of_lt_of_le ((add_lt_add_iff_left β).2 (hκ3 ζ hζ hζX)) hlt.le)
    (fun ζ hζ hζX => hnorm _ (hκ3 ζ hζ hζX).le)
    (fun ζ hζ hζX => ⟨Vh.vhE_add hbE hζ, by
      show κ (b + ζ) ≤ β + κ ζ
      have hk : κ (b + ζ) = κ b + κ ζ := Vh.vhK_add hl hX b hbE ζ hζ
      rw [hk]
      have hb' : κ b = β := hbK
      rw [hb'],
      fun x hx => (xdLtPsi hbn hbm (hx.trans hζX)).trans_le (psi_mono hκ2 (add_le_add le_rfl hx.le)).1⟩)
  -- the iterates over `b` are members of the domain of `κ`
  have hzlt : ∀ n, xdZ S b n < Xh := fun n => (xdZ_lt hbn n).trans_le (by
    rw [xdZ_succ]; exact (psi_mono hκ2 (add_le_add le_rfl (xdZ_lt_Om2 n).le)).1)
  have h11 : RxN S W (1 + 1 : Ordinal.{0}) := RxN.add RxN.one RxN.one
  have hO : RxN S W (Om (1 + 1 : Ordinal.{0})) := RxN.om h11
  have hne : Om (1 + 1 : Ordinal.{0}) ≠ Om 1 := (Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0}))).ne'
  have hzN : ∀ n, RxN S W (xdZ S b n) := by
    intro n
    induction n with
    | zero => exact RxN.zero
    | succ n ih =>
      rw [xdZ_succ]
      refine RxN.psi (InR_Om_succ 1) hne hO (RxN.add hbE.1 ih) ?_
      exact CSet.add_mem ((psi_mono (S := S) hκ2 le_self_add).2 hbn) (CSet.of_lt (xdZ_lt hbn n))
  have hzE : ∀ n, RxE S W (xdZ S b n) := fun n =>
    ⟨hzN n, CSet.of_lt ((hzlt n).trans hθ), ((hzlt n).trans hθ).trans hθW⟩
  have hbig : ∀ ζ, ζ < Xh → S.psi (A + ζ) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om (1 + 1 + 1)) (Om (1 + 1))) := by
    intro ζ hζ
    obtain ⟨n, hn⟩ := (lt_ciSup_iff (xdZ_bdd (S := S) (b := b))).1 (hζ.trans_le (xdX_le_sup hbn hbm))
    have h1 := hlift (xdZ S b n) (hzE n) (hzlt n)
    have h2 := gxTh_mono (Z := upsilon l) (At := ldAtR S l)
      (psi_mono hκ2 (add_le_add (le_refl β) (hκ3 _ (hzE n) (hzlt n)).le)).1
    exact ((psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hn.le)).1.trans h1).trans h2
  have hlim : IsSuccLimit (A + Xh) := isSuccLimit_add _ hXSC.isSuccLimit
  rw [Lw.lw_psi_limit S Low.InR_Om_one hlim]
  refine ciSup_le' fun e => ?_
  rcases lt_or_ge e.1 A with h1 | h1
  · have h0 := hbig 0 hXSC.1
    rw [add_zero] at h0
    exact (psi_mono (S := S) Low.InR_Om_one h1.le).1.trans h0
  · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : e.1 - A < Xh := by
      have h2 := e.2
      change e.1 < A + Xh at h2
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact hbig _ hlt'

/-- **THE LAW AT `k = 0` FOR EVERY BASE `β ∈ D`** (`skX0Law` at `k = 0` with `β ∈ D`):
`Θ(ψ₂(β + Ω₃)) = ψ₁(Â_β + Ω^{X̂⁰_0(β) + Θ 0})` for every own `Â_β` with `Θ(ψ₂(β)) = ψ₁(Â_β)`. -/
theorem xdLaw0D {A β : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 β) :
    Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 β) 0 β := by
  have hlow := xdLow0 hl hX hA hρ hβD hB
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set b := vbT S l β with hbdef
  set Xh := S.psi (b + Om (1 + 1)) (Om (1 + 1)) with hXhdef
  have hW3 : Le.leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  obtain ⟨-, -, -, hnorm, -⟩ := hB
  rw [hW3] at hnorm
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hnorm 0 zero_le; rwa [add_zero] at h
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := xdTr hl hX hβD hβD hβn
  have hbW : b < Om ω := (vbT_mem hl hX hβD).2
  have hAω : Om ω ≤ A := ConjT.OmW_le_A S _
  have hXSC : SC Xh := SC_psi hκ2 _
  have hXε : ω ^ Xh = Xh := gg_SC_eps hXSC
  have hX1 : Om 1 < Xh := (psiS_bounds (S := S) _ 1).1
  have hXω : ω ≤ Xh := (Lw.lw_omega_lt_SC hXSC).le
  -- the upper half
  have hD3 : VbD S l (Om (1 + 1 + 1)) := Wz.wzD_Om3
  have hβ3D : VbD S l (β + Om (1 + 1 + 1)) :=
    ⟨CSet.add_mem hβD.1 hD3.1, CSet.add_mem hβD.2.1 hD3.2.1, vkOmW.1.isPrincipal hβD.2.2 hD3.2.2⟩
  have hT3 : vbT S l (β + Om (1 + 1 + 1)) = b + Om (1 + 1) := by
    rw [Vh.vhT_add hl hX hβD hD3, Wz.wzT_Om3 hl hX]
  have hup := xdUp_at hl hX hA hρ (β + Om (1 + 1 + 1)) hβ3D
  rw [hT3, add_assoc A 1, one_add_of_omega0_le hXω] at hup
  -- the own image of the base
  have hupβ := xdUp_at hl hX hA hρ β hβD
  set B := A + 1 + S.psi b (Om (1 + 1)) with hBdef
  have hAB : A ≤ B := le_self_add.trans le_self_add
  have hBown : B ∈ S.CSet B (S.psi B (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hAB).2 hA) (CSet.one_mem _ _))
      (CSet.psi_mem (hbW.trans_le (hAω.trans hAB)) hκ2 (mxOm2_mem _ _)
        (xdT_leaf hl hX hβD hβn (hAω.trans hAB) hupβ))
  have hψb : 1 + S.psi b (Om (1 + 1)) < Xh := by
    rw [one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 b)).le]
    exact psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right b ldOm2_SC.1)
      ((psi_mono (S := S) hκ2 le_self_add).2 hbn)
  have hρΘ : upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) :=
    (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) _ 1).1.le)
  intro Â hÂ hb
  have hX0 : Wv.wvX0 S l 0 β = Xh := by
    unfold Wv.wvX0; simp only [Nat.cast_zero, zero_add]; rfl
  rw [hX0, gxTh_zero]
  simp only [add_zero]
  rw [Ua.uaOe_fix hXε hX1]
  unfold Le.leTe
  rw [Vn.vnWe_Om3]
  have hAÂ : A ≤ Â := Sf.sfArg_le hA hÂ (by rw [hρ, ← hb]; exact hρΘ)
  have hÂB : Â ≤ B := Sf.sfArg_le hÂ hBown (by rw [← hb]; exact hupβ)
  have hδ : Â - A ≤ 1 + S.psi b (Om (1 + 1)) := by
    rw [Ordinal.sub_le, ← add_assoc]; exact hÂB
  have hab : (Â - A) + Xh = Xh :=
    Ordinal.add_absorp (a := Â - A) (b := Xh) (c := Xh) (by rw [hXε]; exact hδ.trans_lt hψb) (by rw [hXε])
  have hÂX : Â + Xh = A + Xh := by
    calc Â + Xh = A + (Â - A) + Xh := by rw [Ordinal.add_sub_cancel_of_le hAÂ]
      _ = A + Xh := by rw [add_assoc, hab]
  rw [hÂX]
  exact le_antisymm hup hlow

end Rst

/-- `Ro.RoBaseE` at the base `Ω₃` (level `Ω₃`, exponent `0`) at every restart. -/
theorem xdBase_Om3 (l : Ordinal.{0}) : Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 (Om (1 + 1 + 1)) := by
  have hW3 : Le.leWe (Om (1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by rw [add_zero, Vn.vnWe_Om3]
  refine ⟨by rw [hW3], Ry.ryOm3_mem _ _, ?_, fun _ _ => Ry.ryOm3_mem _ _, ?_⟩
  · rw [hW3]
    exact (vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt).trans_le (ConjT.OmW_le_A S _)
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

/-- **Non-vacuity of `xdLaw0D`**: at the restart of `m* = L(0)` with its own `A`, the base `Ω₃` satisfies every
hypothesis (and the law holds there). -/
theorem xdLaw0D_wit (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ VbD S l (Om (1 + 1 + 1)) ∧
      Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 (Om (1 + 1 + 1)) ∧
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := xdWit S
  exact ⟨l, _, _, hl, hX, hA, hρ, Wz.wzD_Om3, xdBase_Om3 l,
    xdLaw0D hl hX hA hρ Wz.wzD_Om3 (xdBase_Om3 l)⟩

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdT_mod
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdT_leaf
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLow0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLaw0D
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdBase_Om3
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdLaw0D_wit
