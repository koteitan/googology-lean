import Googology.Trans.PoR.InaccPsi.R2.KcChain

/-!
# Kd: THE FIRST JUMP IN THE EXPONENT OF `W`: `X → X + W^{Ω₂}`

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdShQ`, `Zd.ZdLaw` as in `Zd.zdSuccQ`.  The exponent `Ω₂` of `W` is
not a code, and `T` jumps there: `T(W^v) = Ω^{Θv}` for the codes `v < Ω₂`, but `T(W^{Ω₂}) = Ω^{Ω₁}`.  The context is
`F(v) = X + W^v` (`Kb.kbLawF`), `R(x) = K + Ω^x`, and

  `Ω^{K + Ω^x} = ω^{Ω₁·K + ω^{Ω₁ + ω^{Ω₁}·x}}`   (`kdOe2`),

a THREE-level tower of `Ka.KaT`.

* `kdOe2`, `kdShW2` (**`X + W^{Ω₂}` is a shift**, `T = K + Ω^{Ω₁}`),
* `kdLaw` (**THE JUMP `X → X + W^{Ω₂}`**: the law at every `X + W^v`, `v` a code, gives the law at `X + W^{Ω₂}`),
* `kdLawAll` (the law at every `X + W^{Ω₂} + e`), `kdTop` (**THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^{Ω₂} + e`**,
  over `Kc.kcTop`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz
  Googology.Trans.PoR.InaccPsi.R2.Kb Googology.Trans.PoR.InaccPsi.R2.Kc

variable {S : InaccSeq.{0}}

/-- `Ω^{K + Ω^x} = ω^{Ω₁·K + ω^{Ω₁ + ω^{Ω₁}·x}}`. -/
theorem kdOe2 (K x : Ordinal.{0}) : leOe (K + leOe x) = ω ^ (Om 1 * K + ω ^ (Om 1 + ω ^ Om 1 * x)) := by
  unfold leOe
  congr 1
  rw [mul_add, opow_add, Om1_opow]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
theorem kd_Om2D : VbD S l (Om (1 + 1 : Ordinal.{0})) := by
  have h := vbD_Om (S := S) (l := l) 1; rwa [Nat.cast_one] at h

theorem kd_TOm2 : vbT S l (Om (1 + 1 : Ordinal.{0})) = Om 1 := by
  have h := vbT_Om (S := S) hl hX (k := 1) le_rfl; rwa [Nat.cast_one] at h

/-- `T(X + W^v) = K + Ω^{Θv}`, `X + W^v ∈ D`, for a code `v < θ`. -/
theorem kdT_v {X K q v : Ordinal.{0}} (hs : ZdShQ S l X K q) (hv : GxCl (upsilon l) (ldAtR S l) v)
    (hvθ : v < ConjT.th S) :
    VbD S l (X + leWe v) ∧ vbT S l (X + leWe v) = K + leOe (gxTh (upsilon l) (ldAtR S l) v) := by
  have hvx := zxEx_code hl hX hv hvθ
  obtain ⟨hWD, hWT⟩ := zxTW hl hX hvx.D
  refine ⟨⟨CSet.add_mem hs.memH hWD.1, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) hWD.2.1,
    vkOmW.1.isPrincipal hs.lt hWD.2.2⟩, ?_⟩
  rw [Vh.vhT_add hl hX hs.D hWD, hs.T, hWT, hvx.T]

/-- **`X + W^{Ω₂}` is a shift**, `T(X + W^{Ω₂}) = K + Ω^{Ω₁}`, with the threshold of `X`. -/
theorem kdShW2 {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) :
    ZdShQ S l (X + leWe (Om (1 + 1))) (K + leOe (Om 1)) q := by
  obtain ⟨hWD, hWT⟩ := zxTW hl hX (kd_Om2D (S := S) (l := l))
  have hKm : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c →
      K + leOe (Om 1) ∈ S.CSet a c := fun a c h hq =>
    CSet.add_mem (hs.Km a c h hq) (leOe_mem (CSet.Om_mem (CSet.one_mem _ _)))
  refine ⟨fun a c h hq => CSet.add_mem (hs.mem a c h hq) (leWe_mem (mxOm2_mem a c)),
    vkOmW.1.isPrincipal hs.lt hWD.2.2, ?_, hKm,
    fun a c h hq => ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hKm a c h hq),
    hs.Kpos.trans_le le_self_add, CSet.add_mem hs.memH hWD.1, hs.qc, hs.qθ⟩
  rw [Vh.vhT_add hl hX hs.D hWD, hs.T, hWT, kd_TOm2 hl hX]

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE JUMP `X → X + W^{Ω₂}`**: the law at every `X + W^v` (`v` a code below `θ` with `v' < ψ₂(β + W^{X + W^{v'}})`
for every code `v' ≤ v`) over `β` gives the law at `X + W^{Ω₂}`. -/
theorem kdLaw {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hB : Ro.RoBaseE S l (X + leWe (Om (1 + 1))) 0 β) (hq : q < S.psi (β + leWe X) (Om (1 + 1)))
    (Hv : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S →
      (∀ v', GxCl (upsilon l) (ldAtR S l) v' → v' ≤ v → v' < S.psi (β + leWe (X + leWe v')) (Om (1 + 1))) →
      Ro.RoBaseE S l (X + leWe v) 0 β → ZdLaw S l A (X + leWe v) 0 β) :
    ZdLaw S l A (X + leWe (Om (1 + 1))) 0 β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hB0 := hB
  unfold Ro.RoBaseE at hB0
  simp only [add_zero] at hB0
  obtain ⟨-, -, -, hβown, -⟩ := hB0
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  have hs2 := kdShW2 hl hX hs
  obtain ⟨hWXD, -⟩ := zxTW hl hX hs.D
  have hβXD : VbD S l (β + leWe X) :=
    ⟨CSet.add_mem hβD.1 hWXD.1, CSet.add_mem hβD.2.1 hWXD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWXD.2.2⟩
  have hqΩ : gxTh (upsilon l) (ldAtR S l) q < Om 1 := kbTh_lt hl hX hA hρ hs.qc hβXD hq
  have hΩa : ∀ a : Ordinal.{0}, Om 1 < S.psi a (Om (1 + 1)) := fun a => (psiS_bounds (S := S) _ 1).1
  set b := vbT S l β with hbdef
  set t := Ka.KaT.up (Om 1 * K) (Ka.KaT.base (Om 1) (Om 1)) with htdef
  have hfun : (fun x => b + leOe (K + leOe x)) = (Ka.KaT.up b t).ev := by
    funext x; rw [Ka.KaT.ev_up, Ka.KaT.ev_up, Ka.KaT.ev_base, kdOe2]
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  have hOm1m : ∀ a c : Ordinal.{0}, Om 1 ∈ S.CSet a c := fun a c => CSet.Om_mem (CSet.one_mem _ _)
  refine kbLawF hl hX hA hρ (F := fun v => X + leWe v) (R := fun x => K + leOe x)
    (E := X + leWe (Om (1 + 1))) (q := q)
    (fun v hv hvθ => (kdT_v hl hX hs hv hvθ).1)
    (fun v hv => add_le_add le_rfl (leWe_mono hv.le))
    (fun _ _ hab => (add_lt_add_iff_left X).2 (leWe_lt hab))
    (fun a c v h1 hqc hv => CSet.add_mem (hs.mem a c h1 hqc) (leWe_mem (CSet.of_lt hv)))
    hs.qc hs2.D (fun v hv hvθ => (kdT_v hl hX hs hv hvθ).2) hs2.T
    (fun _ _ h' => add_le_add le_rfl (Yy.yyOe_mono h')) hβD hB
    (hq.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1)
    (fun a _ _ => ?_) ?_ Hv
  · have hg := Ka.KaT.gap (S := S) (a := a) (Ka.KaT.up b t) (hOm1m _ _)
    rw [← hfun] at hg
    exact hg
  · have hst := Ka.KaT.step (S := S) hbn t
      ⟨fun a _ => hs.Km1 a _ (hρ1.trans (hΩa a)).le (hqΩ.trans (hΩa a)),
        fun a _ => hOm1m _ _, fun a _ => hOm1m _ _⟩
    rw [← hfun] at hst
    exact hst

/-- **The law at every exponent `X + W^{Ω₂} + e`**, from the law at every `X + W^v` on the bases with `Q`. -/
theorem kdLawAll {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) (Q : Ordinal.{0} → Prop)
    (hQq : ∀ β, Q β → q < S.psi (β + leWe X) (Om (1 + 1))) (hQup : ∀ β β', β ≤ β' → Q β → Q β')
    (Hv : ∀ β, VbD S l β → Q β → ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S →
      (∀ v', GxCl (upsilon l) (ldAtR S l) v' → v' ≤ v → v' < S.psi (β + leWe (X + leWe v')) (Om (1 + 1))) →
      Ro.RoBaseE S l (X + leWe v) 0 β → ZdLaw S l A (X + leWe v) 0 β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (X + leWe (Om (1 + 1))) e β → Q β → ZdLaw S l A (X + leWe (Om (1 + 1))) e β :=
  zdTopUpQ hl hX hA hρ (kdShW2 hl hX hs) Q (fun β hQ => (hQq β hQ).trans_le
    (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono le_self_add))).1) hQup
    fun β hβD hB hQ => kdLaw hl hX hA hρ hs hβD hB (hQq β hQ) (Hv β hβD hQ)

/-- **THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + W^{Ω₂} + e`** (`e < Ω₂` a code, `β ∈ D` a base of exponent `e`). -/
theorem kdTop (k : ℕ) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (Om (1 + 1))) e β →
        ZdLaw S l A (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe (Om (1 + 1))) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hs := (zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1
  intro e hec he2 β hβD hB
  refine kdLawAll hl hX hA hρ hs (fun _ => True) (fun _ _ => (SC_psi hκ2 _).1) (fun _ _ _ _ => trivial)
    (fun β hβD _ v hv hvθ hown hBv => ?_) e hec he2 β hβD hB trivial
  rcases eq_or_ne v 0 with rfl | hne
  · -- `v = 0`: `X + W^0 = X + 1`, the code `1` over `X`
    have hB1 : Ro.RoBaseE S l X 1 β := by
      unfold Ro.RoBaseE at hBv ⊢
      rw [add_zero, leWe_zero] at hBv
      obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hBv
      exact ⟨hβd, hβH, hβA, hβown, fun e' _ he' =>
        (he'.trans_lt (gg_one_lt_of_SC Ph.ph_SC_Om1)).trans (psiS_bounds (S := S) _ 1).1⟩
    have h := xmTopUp S k l ηx A hl hX hA hρ 1 β (GxCl.small (gg_one_lt_of_SC hρSC))
      (gg_one_lt_of_SC ldOm2_SC) hβD hB1
    unfold ZdLaw leTe at h ⊢
    rw [leWe_zero, add_zero]
    exact h
  · -- `v ≥ 1`: the chain of `W^v` at the coefficient `1`
    have hv1 : 1 ≤ v := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)
    have hE : KcE S l X v β := fun h' hc _ hle => hown h' hc hle
    have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
    have h := kcTop hl hX hA hρ k v hv hv1 hvθ 1 h1c (gg_one_lt_of_SC (ConjT.SC_th S)) 0
      (GxCl.zero hρSC.1) ldOm2_SC.1 β hβD (by rw [mul_one]; exact hBv)
      ⟨hE, hown v hv le_rfl, fun u' _ hu' =>
        hu'.trans_lt ((gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) _ 1).1)⟩
    rwa [mul_one] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kd.kdLaw
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kd.kdTop
