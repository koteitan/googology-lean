import Googology.Trans.PoR.InaccPsi.R2.KdOm2

/-!
# Ke: THE CONTEXTS OF THE JUMPS, of any depth, and the jump at every context

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdLaw`, `Zx.ZxEx` (exponent data), `Ka.KaT` (towers) as before.
A context `KeCtx λ C g R t q` is a strictly increasing map `C` of the codes into `D` below `g` with `T(C v) = R(Θv)`,
`T g = R(Ω₁)`, `Ω₁·R(x) = t(x)` for a tower `t`, the constants in the closures once the threshold `q` and its reading
are below the bound.  Contexts are closed under

* `keCtx_base` (`v ↦ g₀ + W^j·v`, `R(x) = T g₀ + Ω^{T j}·x`, the tower `Ω₁·Tg₀ + ω^{Ω₁ + Ω₁·Tj}·x`), and
* `keCtx_nest` (`v ↦ g₁ + W^{C'(v)}`, `R(x) = T g₁ + Ω^{R'(x)}`, the tower `Ω₁·Tg₁ + ω^{Ω₁ + t'(x)}`),

so every nesting `X + W^{h₁ + W^{h₂ + … + W^{j}·v}}` is a context.  `keLaw` (**THE JUMP AT EVERY CONTEXT**: the law at
every `C v` over `β` gives the law at `g`; `Kb.kbLawF` with the gap and the step of the tower `Tβ + ω^{t(x)}`).
`Kb.kbLawJ` is the base context over a shift, `Kd.kdLaw` the nest of the base `v ↦ v` over a shift.

* `ZdShQ.toEx` (a shift is exponent data), `keCtx_id` (`v ↦ v`), `keCtx_jump` (**the exponent jump**
  `X + W^{h₁ + W^{j+1}}` over the context `v ↦ X + W^{h₁ + W^j·v}`).

No new axiom.  New definition: `KeCtx` (the contexts).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ke

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Kb
  Googology.Trans.PoR.InaccPsi.R2.Ka

variable {S : InaccSeq.{0}}

/-- **A context of a jump.** -/
structure KeCtx (S : InaccSeq.{0}) (l : Ordinal.{0}) (C : Ordinal.{0} → Ordinal.{0}) (g : Ordinal.{0})
    (R : Ordinal.{0} → Ordinal.{0}) (t : KaT) (q : Ordinal.{0}) : Prop where
  D : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → VbD S l (C v)
  le : ∀ v, v < Om (1 + 1) → C v ≤ g
  sm : StrictMono C
  mem : ∀ a c v : Ordinal.{0}, Om 1 ≤ c → q < c → v < c → C v ∈ S.CSet a c
  T : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → vbT S l (C v) = R (gxTh (upsilon l) (ldAtR S l) v)
  Tg : vbT S l g = R (Om 1)
  gD : VbD S l g
  Rmono : Monotone R
  ev : ∀ x, Om 1 * R x = t.ev x
  bm : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c → t.bm ∈ S.CSet a c
  consts : t.InC fun y => ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c → y ∈ S.CSet a c
  qc : GxCl (upsilon l) (ldAtR S l) q
  qθ : q < ConjT.th S

/-- A shift is exponent data. -/
theorem ZdShQ.toEx {l X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) : ZxEx S l X K q :=
  ⟨hs.D, hs.T, hs.mem, hs.Km, hs.qc, hs.qθ⟩

theorem KaT.addC_bm (a : Ordinal.{0}) (t : KaT) : (KaT.addC a t).bm = t.bm := by cases t <;> rfl

theorem KaT.addC_InC {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) (hadd : ∀ c, P a → P c → P (a + c)) :
    ∀ t : KaT, t.InC P → (KaT.addC a t).InC P
  | KaT.base _ _, hC => ⟨hadd _ ha hC.1, hC.2⟩
  | KaT.up _ _, hC => ⟨hadd _ ha hC.1, hC.2⟩

theorem ke_Om1_mul_Oe (x : Ordinal.{0}) : Om 1 * leOe x = ω ^ (Om 1 + Om 1 * x) := by
  unfold leOe; rw [opow_add, Om1_opow]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The base context** `v ↦ g₀ + W^j·v`. -/
theorem keCtx_base {g₀ G₀ q₀ j J qj : Ordinal.{0}} (hg : ZxEx S l g₀ G₀ q₀) (hj : ZxEx S l j J qj) :
    KeCtx S l (fun v => g₀ + leWe j * v) (g₀ + leWe (j + 1)) (fun x => G₀ + leOe J * x)
      (KaT.base (Om 1 * G₀) (Om 1 + Om 1 * J)) (max q₀ qj) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  have hj1 : j + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hj.D.2.2
  have hj1D : VbD S l (j + 1) := ⟨CSet.succ_mem hj.D.1, CSet.succ_mem hj.D.2.1, hj1⟩
  obtain ⟨hW1D, hW1T⟩ := zxTW hl hX hj1D
  have hWv : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → VbD S l (leWe j * v) ∧
      vbT S l (leWe j * v) = leOe J * gxTh (upsilon l) (ldAtR S l) v := by
    intro v hv hvθ
    have hv2 : v < Om (1 + 1) := hvθ.trans (psi_lt (InR_Om_succ 1) _)
    have hvH : v ∈ cdHull S l := (ldHull_iff hl hX hv2).2 hv
    refine ⟨⟨leMulWe_mem hj.D.1 hvH, leMulWe_mem hj.D.2.1 (CSet.of_lt hvθ),
      (leMulWe_mono hv2.le).trans_lt (by rw [← leWe_succ]; exact (leWe_lt_SC vkOmW.1 vkOmW.2 hj1).1)⟩, ?_⟩
    have h := Vh.vhT_cnfW hl hX hj.D (Xi.xiD_zero l) hvH hv2
    rwa [add_zero, Vh.vhT_zero hl hX, add_zero, hj.T] at h
  have hmaxΘ : ∀ c, gxTh (upsilon l) (ldAtR S l) (max q₀ qj) < c →
      gxTh (upsilon l) (ldAtR S l) q₀ < c ∧ gxTh (upsilon l) (ldAtR S l) qj < c := fun c h =>
    ⟨(gxTh_mono (le_max_left _ _)).trans_lt h, (gxTh_mono (le_max_right _ _)).trans_lt h⟩
  have hbm : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) (max q₀ qj) < c →
      Om 1 + Om 1 * J ∈ S.CSet a c := fun a c h hq =>
    CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hj.Hm a c h (hmaxΘ c hq).2))
  refine ⟨fun v hv hvθ => ?_, fun v hv => add_le_add le_rfl (by rw [leWe_succ]; exact leMulWe_mono hv.le),
    fun _ _ hab => (add_lt_add_iff_left g₀).2 (mul_lt_mul_of_pos_left hab (leWe_pos j)),
    fun a c v h1 hq hv => CSet.add_mem (hg.mem a c h1 ((le_max_left _ _).trans_lt hq))
      (leMulWe_mem (hj.mem a c h1 ((le_max_right _ _).trans_lt hq)) (CSet.of_lt hv)),
    fun v hv hvθ => by rw [Vh.vhT_add hl hX hg.D (hWv v hv hvθ).1, hg.T, (hWv v hv hvθ).2], ?_,
    ⟨CSet.add_mem hg.D.1 hW1D.1, CSet.add_mem hg.D.2.1 hW1D.2.1, vkOmW.1.isPrincipal hg.D.2.2 hW1D.2.2⟩,
    fun _ _ h => add_le_add le_rfl (mul_le_mul_right h _), fun x => ?_, hbm,
    ⟨fun a c h hq => ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hg.Hm a c h (hmaxΘ c hq).1), hbm⟩,
    zy_max_code hg.qc hj.qc, max_lt hg.qθ hj.qθ⟩
  · have hvD := (hWv v hv hvθ).1
    exact ⟨CSet.add_mem hg.D.1 hvD.1, CSet.add_mem hg.D.2.1 hvD.2.1, vkOmW.1.isPrincipal hg.D.2.2 hvD.2.2⟩
  · have hTj1 : vbT S l (j + 1) = J + 1 := by rw [Vh.vhT_add hl hX hj.D h1D, hj.T, hT1]
    rw [Vh.vhT_add hl hX hg.D hW1D, hg.T, hW1T, hTj1, leOe_succ]
  · rw [KaT.ev_base, mul_add, ← mul_assoc, ke_Om1_mul_Oe]

/-- **The nested context** `v ↦ g₁ + W^{C'(v)}`. -/
theorem keCtx_nest {g₁ G₁ q₁ : Ordinal.{0}} {C' : Ordinal.{0} → Ordinal.{0}} {g' : Ordinal.{0}}
    {R' : Ordinal.{0} → Ordinal.{0}} {t' : KaT} {q' : Ordinal.{0}} (hg : ZxEx S l g₁ G₁ q₁)
    (hC : KeCtx S l C' g' R' t' q') :
    KeCtx S l (fun v => g₁ + leWe (C' v)) (g₁ + leWe g') (fun x => G₁ + leOe (R' x))
      (KaT.up (Om 1 * G₁) (KaT.addC (Om 1) t')) (max q₁ q') := by
  have hmaxΘ : ∀ c, gxTh (upsilon l) (ldAtR S l) (max q₁ q') < c →
      gxTh (upsilon l) (ldAtR S l) q₁ < c ∧ gxTh (upsilon l) (ldAtR S l) q' < c := fun c h =>
    ⟨(gxTh_mono (le_max_left _ _)).trans_lt h, (gxTh_mono (le_max_right _ _)).trans_lt h⟩
  have hD : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → VbD S l (g₁ + leWe (C' v)) := by
    intro v hv hvθ
    obtain ⟨hWD, -⟩ := zxTW hl hX (hC.D v hv hvθ)
    exact ⟨CSet.add_mem hg.D.1 hWD.1, CSet.add_mem hg.D.2.1 hWD.2.1, vkOmW.1.isPrincipal hg.D.2.2 hWD.2.2⟩
  obtain ⟨hWgD, hWgT⟩ := zxTW hl hX hC.gD
  refine ⟨hD, fun v hv => add_le_add le_rfl (leWe_mono (hC.le v hv)),
    fun _ _ hab => (add_lt_add_iff_left g₁).2 (leWe_lt (hC.sm hab)),
    fun a c v h1 hq hv => CSet.add_mem (hg.mem a c h1 ((le_max_left _ _).trans_lt hq))
      (leWe_mem (hC.mem a c v h1 ((le_max_right _ _).trans_lt hq) hv)),
    fun v hv hvθ => ?_, by rw [Vh.vhT_add hl hX hg.D hWgD, hg.T, hWgT, hC.Tg],
    ⟨CSet.add_mem hg.D.1 hWgD.1, CSet.add_mem hg.D.2.1 hWgD.2.1, vkOmW.1.isPrincipal hg.D.2.2 hWgD.2.2⟩,
    fun _ _ h => add_le_add le_rfl (Yy.yyOe_mono (hC.Rmono h)), fun x => ?_,
    fun a c h hq => by rw [KaT.bm, KaT.addC_bm]; exact hC.bm a c h (hmaxΘ c hq).2, ?_,
    zy_max_code hg.qc hC.qc, max_lt hg.qθ hC.qθ⟩
  · obtain ⟨hWD, hWT⟩ := zxTW hl hX (hC.D v hv hvθ)
    rw [Vh.vhT_add hl hX hg.D hWD, hg.T, hWT, hC.T v hv hvθ]
  · rw [KaT.ev_up, KaT.addC_ev, mul_add, ke_Om1_mul_Oe, hC.ev]
  · refine ⟨fun a c h hq => ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hg.Hm a c h (hmaxΘ c hq).1),
      KaT.addC_InC (fun a c _ _ => CSet.Om_mem (CSet.one_mem _ _))
        (fun _ h1 h2 a c hc hq => CSet.add_mem (h1 a c hc hq) (h2 a c hc hq)) t' ?_⟩
    exact KaT.InC.imp (fun y hy a c hc hq => hy a c hc (hmaxΘ c hq).2) t' hC.consts

/-- The identity context `v ↦ v` (`g₀ = 0`, `j = 0`). -/
theorem keCtx_id :
    KeCtx S l (fun v => 0 + leWe 0 * v) (0 + leWe (0 + 1)) (fun x => 0 + leOe 0 * x)
      (KaT.base (Om 1 * 0) (Om 1 + Om 1 * 0)) (max 0 0) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0x : ZxEx S l 0 0 0 := by
    have h := zxEx_nat hl hX (S := S) 0; rwa [Nat.cast_zero] at h
  exact keCtx_base hl hX h0x h0x

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE JUMP AT EVERY CONTEXT**: the law at every `C v` over `β` gives the law at `g`. -/
theorem keLaw {C : Ordinal.{0} → Ordinal.{0}} {g : Ordinal.{0}} {R : Ordinal.{0} → Ordinal.{0}} {t : KaT}
    {q : Ordinal.{0}} (hC : KeCtx S l C g R t q) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hB : Ro.RoBaseE S l g 0 β) (hq : q < S.psi (β + leWe (C 1)) (Om (1 + 1)))
    (Hu : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S →
      (∀ v', GxCl (upsilon l) (ldAtR S l) v' → v' ≤ v → v' < S.psi (β + leWe (C v')) (Om (1 + 1))) →
      Ro.RoBaseE S l (C v) 0 β → ZdLaw S l A (C v) 0 β) :
    ZdLaw S l A g 0 β := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hB0 := hB
  unfold Ro.RoBaseE at hB0
  simp only [add_zero] at hB0
  obtain ⟨-, -, -, hβown, -⟩ := hB0
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
  obtain ⟨hW1D, -⟩ := zxTW hl hX (hC.D 1 h1c h1θ)
  have hβ1D : VbD S l (β + leWe (C 1)) :=
    ⟨CSet.add_mem hβD.1 hW1D.1, CSet.add_mem hβD.2.1 hW1D.2.1, vkOmW.1.isPrincipal hβD.2.2 hW1D.2.2⟩
  have hqΩ : gxTh (upsilon l) (ldAtR S l) q < Om 1 := kbTh_lt hl hX hA hρ hC.qc hβ1D hq
  have hΩa : ∀ a : Ordinal.{0}, Om 1 < S.psi a (Om (1 + 1)) := fun a => (psiS_bounds (S := S) _ 1).1
  set b := vbT S l β with hbdef
  have hfun : (fun x => b + leOe (R x)) = (KaT.up b t).ev := by
    funext x; rw [KaT.ev_up, ← hC.ev]; rfl
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  refine kbLawF hl hX hA hρ (F := C) (R := R) (E := g) (q := q) hC.D hC.le hC.sm hC.mem hC.qc hC.gD hC.T hC.Tg
    hC.Rmono hβD hB hq (fun a hρa hqa => ?_) ?_ Hu
  · have hg := KaT.gap (S := S) (a := a) (KaT.up b t) (hC.bm a _ hρa hqa)
    rw [← hfun] at hg
    exact hg
  · have hst := KaT.step (S := S) hbn t
      (KaT.InC.imp (fun y hy a _ => hy a _ (hρ1.trans (hΩa a)).le (hqΩ.trans (hΩa a))) t hC.consts)
    rw [← hfun] at hst
    exact hst

/-- **THE EXPONENT JUMP** `X + W^{h₁ + W^{j+1}}` over the context `v ↦ X + W^{h₁ + W^j·v}` (`X` a shift, `h₁`, `j`
exponent data): the law at every `X + W^{h₁ + W^j·v}` over `β` gives the law at `X + W^{h₁ + W^{j+1}}`. -/
theorem keJumpExp {X K q h₁ H₁ q₁ j J qj : Ordinal.{0}} (hs : ZdShQ S l X K q) (h1x : ZxEx S l h₁ H₁ q₁)
    (hjx : ZxEx S l j J qj) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hB : Ro.RoBaseE S l (X + leWe (h₁ + leWe (j + 1))) 0 β)
    (hq : max q (max q₁ qj) < S.psi (β + leWe (X + leWe (h₁ + leWe j * 1))) (Om (1 + 1)))
    (Hu : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S →
      (∀ v', GxCl (upsilon l) (ldAtR S l) v' → v' ≤ v →
        v' < S.psi (β + leWe (X + leWe (h₁ + leWe j * v'))) (Om (1 + 1))) →
      Ro.RoBaseE S l (X + leWe (h₁ + leWe j * v)) 0 β → ZdLaw S l A (X + leWe (h₁ + leWe j * v)) 0 β) :
    ZdLaw S l A (X + leWe (h₁ + leWe (j + 1))) 0 β :=
  keLaw hl hX hA hρ (keCtx_nest hl hX (ZdShQ.toEx hs) (keCtx_base hl hX h1x hjx)) hβD hB hq Hu

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ke

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ke.keLaw
#print axioms Googology.Trans.PoR.InaccPsi.R2.Ke.keJumpExp
