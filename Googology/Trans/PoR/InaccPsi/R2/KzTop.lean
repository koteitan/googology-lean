import Googology.Trans.PoR.InaccPsi.R2.KzOff

/-!
# Kz: THE TOP LAW ON `D_K` BELOW `A` (`Kx.kxTop` below a bound `K`)

`Θ`, `T_K = vbTK S λ K`, `D_K = VbDK S λ K`, `κ = Vb.vbK`, `A` own with `ψ₁(A) = ρ_λ`.

* `KuNK` (**the bases**: `b ∈ D_K` normal, `Ω₃ ∣ b`, `Ω₃ ≤ b`), `KuLawK` (**the top law at `b`**:
  `Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T_K b))`);
* `kzZ_lt` (`Θ(ψ₂ b) < Ω₁` for `b ∈ D_K`, `b < A`, from `Kz.kzUp_at`);
* `kzLowG` (**THE TOP LAW FROM ONE DOMINATION CONDITION**: `Kz.kzLow` with any atom `ψ₂ a < ψ₂ b` above
  `ψ₁(A + ξ)`);
* `kzLim` (**the limit quotients `b/Ω₃`**: `Kx.kxLim` on `D_K`, with `Kz.kzKx`, `Kz.kzNorm`);
* `kzSucc` (**`b = β' + Ω₃`, `β' ≠ 0`**: for `ξ ≤ ψ₂(T_K β')` the law at `β'`; above it `ξ = ψ₂(T_K β') + ζ` and the lift
  `Kz.kzLiftK` at the base `β'` gives `ψ₁(A + ξ) ≤ Θ(ψ₂(β' + κ ζ))`);
* `kzTop` (**THE TOP LAW AT EVERY `b ∈ KuNK` BELOW `A`**; `b = Ω₃` from `Kx.kxTop`).

No new axiom.  New definitions: `KuNK`, `KuLawK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Vb
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ku
  Googology.Trans.PoR.InaccPsi.R2.Kx Googology.Trans.PoR.InaccPsi.R2.Kw Googology.Trans.PoR.InaccPsi.R2.Xd

variable {S : InaccSeq.{0}}

/-- **The bases below `K`.** -/
def KuNK (S : InaccSeq.{0}) (l K b : Ordinal.{0}) : Prop :=
  VbDK S l K b ∧ b ∈ S.CSet b (S.psi b (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ b ∧ Om (1 + 1 + 1) ≤ b

/-- **The top law at `b` below `K`.** -/
def KuLawK (S : InaccSeq.{0}) (l K A b : Ordinal.{0}) : Prop :=
  gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
    S.psi (A + 1 + S.psi (vbTK S l K b) (Om (1 + 1))) (Om 1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hKB hA hρ

theorem kzZ_lt {b : Ordinal.{0}} (hbD : VbDK S l K b) (hbA : b < A) :
    gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) < Om 1 :=
  (kzUp_at hl hX hKB hA hρ b hbD hbA).trans_lt (psi_lt Low.InR_Om_one _)

/-- **THE TOP LAW FROM ONE DOMINATION CONDITION.** -/
theorem kzLowG {b : Ordinal.{0}} (hbD : VbDK S l K b) (hbA : b < A)
    (hfam : ∀ ξ, HCl S (A + 1 + S.psi (vbTK S l K b) (Om (1 + 1)))
        (gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1)))) ξ → ξ < S.psi (vbTK S l K b) (Om (1 + 1)) →
      ∃ a, VbDK S l K a ∧ a < A ∧ S.psi a (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧
        S.psi (A + ξ) (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) :
    KuLawK S l K A b := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hup := kzUp_at hl hX hKB hA hρ b hbD hbA
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZdef
  set P := S.psi (vbTK S l K b) (Om (1 + 1)) with hPdef
  have hZ : SC Z := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
  have hPω : ω ≤ P := (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le
  refine le_antisymm hup (psi_le_of_key hZ fun e he heA => ?_)
  rcases lt_or_ge e A with h1 | h1
  · have hρZ : upsilon l < Z := by
      have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om (psiS_bounds (S := S) b 1).1
      rwa [gxTh_Om1 hZρ hZ1 hAt] at h
    exact ((psi_mono hκ1 h1.le).1.trans_eq hρ).trans_lt hρZ
  · set ξ := e - A with hξdef
    have e1 : e = A + ξ := (Ordinal.add_sub_cancel_of_le h1).symm
    have hξP : ξ < P := by
      have h2 : A + ξ < A + (1 + P) := by rw [← e1, ← add_assoc]; exact heA
      have h3 := (add_lt_add_iff_left A).1 h2
      rwa [one_add_of_omega0_le hPω] at h3
    have hξH : HCl S (A + 1 + P) Z ξ := Kt.ktHCl_sub e he A
    obtain ⟨a, haD, haA, hab, hle⟩ := hfam ξ hξH hξP
    rw [e1]
    have hAeq : A = ConjT.Aη S (cdEta S l) := (Wg.wgOwnEta hl hX hA hρ).2
    have hab' : a < b := by
      by_contra hc; push Not at hc; exact absurd hab (not_lt.2 (psi_mono hκ2 hc).1)
    have hat : S.psi a (Om (1 + 1)) ∈ ldAtR S l := ⟨a, haD.1, hAeq ▸ haA, rfl⟩
    exact hle.trans_lt (gxTh_lt (GxCl.atom hat) hab)

/-- **THE TOP LAW AT EVERY LIMIT `Ω₃`-QUOTIENT FROM THE LAW BELOW, ON `D_K`.** -/
theorem kzLim {b : Ordinal.{0}} (hb : KuNK S l K b) (hbA : b < A)
    (hq : ∀ y, y < b → Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) < b)
    (IH : ∀ a, KuNK S l K a → a < b → KuLawK S l K A a) : KuLawK S l K A b := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAeq : A = ConjT.Aη S (cdEta S l) := (Wg.wgOwnEta hl hX hA hρ).2
  obtain ⟨hbD, hbn, -, hb3le⟩ := hb
  set Zb := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZbdef
  set P := S.psi (vbTK S l K b) (Om (1 + 1)) with hPdef
  set α := A + 1 + P with hαdef
  have hZ : SC Zb := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZρ1.trans (psiS_bounds (S := S) _ 1).1)
  have hZ1 : Zb < Om 1 := kzZ_lt hl hX hKB hA hρ hbD hbA
  have hZL : Zb ≤ S.Lam := (hZ1.trans (Om_lt_Om.2 (lt_add_one 1))).le.trans Xd.xdOm2_le_Lam
  have hZW : Zb ≤ vbW S l := by rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 b).le
  have hbK : b < K := hbD.2.2
  have hO3 : ∀ x y : Ordinal.{0}, Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet x y := fun x y =>
    CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem x y)))
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this; rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  have h3SC : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne'
  have h3e : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) := gg_SC_eps h3SC
  obtain ⟨hTbE, hTbK⟩ := vbTK_eq hl hX hKB hbD
  set 𝒴 : Set Ordinal.{0} :=
    {y | ∃ a, KuNK S l K a ∧ a < b ∧ y = S.psi (vbTK S l K a) (Om (1 + 1))} with h𝒴
  have h3N : KuNK S l K (Om (1 + 1 + 1)) :=
    ⟨⟨hO3 _ _, hO3 _ _, h3W.trans_le hKB.ge⟩, hO3 _ _, dvd_refl _, le_rfl⟩
  have h3b : Om (1 + 1 + 1 : Ordinal.{0}) < b := by
    have h := hq 0 ((Om_pos (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne').trans_le
      hb3le)
    rwa [Ordinal.zero_div, mul_zero, zero_add] at h
  have hne : ∃ y, y ∈ 𝒴 := ⟨_, Om (1 + 1 + 1), h3N, h3b, rfl⟩
  have hSC : ∀ y ∈ 𝒴, SC y ∧ Om 1 < y := by
    rintro y ⟨a, -, -, rfl⟩
    exact ⟨SC_psi hκ2 _, (psiS_bounds (S := S) _ 1).1⟩
  have hdir : ∀ y₁ ∈ 𝒴, ∀ y₂ ∈ 𝒴, ∃ y ∈ 𝒴, y₁ ≤ y ∧ y₂ ≤ y := by
    rintro y₁ ⟨a₁, h1N, h1b, rfl⟩ y₂ ⟨a₂, h2N, h2b, rfl⟩
    rcases le_total a₁ a₂ with h | h
    · exact ⟨_, ⟨a₂, h2N, h2b, rfl⟩, (psi_mono hκ2 ((vbTK_le_iff hl hX hKB h1N.1 h2N.1).1 h)).1, le_rfl⟩
    · exact ⟨_, ⟨a₁, h1N, h1b, rfl⟩, le_rfl, (psi_mono hκ2 ((vbTK_le_iff hl hX hKB h2N.1 h1N.1).1 h)).1⟩
  have hsub : ∀ e, HCl S α Zb e → e < α → S.psi e (Om (1 + 1)) < P →
      ∃ y ∈ 𝒴, S.psi e (Om (1 + 1)) < y := by
    intro e he heα hψe
    have heL : e < S.Lam := lt_Lam_of_mem hZL (HCl.mem_CSet he)
    set es := S.M e (S.psi e (Om (1 + 1))) e with hesdef
    obtain ⟨-, hees⟩ := M_spec (e := e) (g := S.psi e (Om (1 + 1))) heL
    have hψes : S.psi es (Om (1 + 1)) = S.psi e (Om (1 + 1)) := psi_M_eq hκ2 heL
    have hesn : es ∈ S.CSet es (S.psi es (Om (1 + 1))) := M_mem_self hκ2 heL
    have hZg : Zb ≤ S.psi e (Om (1 + 1)) := (hZ1.trans (psiS_bounds (S := S) e 1).1).le
    have hesH : HCl S α Zb es :=
      rxM_mem_of_Good (rxClosed_HCl heα.le hZL) e heL (rxMQ_of_mem_HCl heα.le hZg hZL he).1.1
    have hesT : es < vbTK S l K b := by
      by_contra hc
      push Not at hc
      exact absurd hψe (not_lt.2 (hψes ▸ (psi_mono hκ2 hc).1))
    have hesK : es < K := hesT.trans hTbE.2.2
    have hesE : RxEK S Zb K es :=
      ⟨rxN_of_HCl hZ1.le hesH, CSet_mono hesK.le (psi_mono hκ2 hesK.le).1 hesn, hesK⟩
    have hesC : es ∈ S.CSet (vbTK S l K b) P := CSet_mono hesT.le (psi_mono hκ2 hesT.le).1 hesn
    have harg : ∀ d, RxEK S (rxW (upsilon l) (ldAtR S l)) K d → d < vbTK S l K b →
        rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) d < b := fun d hd hdb => by
      have h := vbKK_mono hl hX hKB hd hTbE hdb
      rwa [hTbK] at h
    have hyC : vbK S l es ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
      kzKx hZρ hZρ1 hAt hKB hZ hZW (fun g hg => CSet.of_lt (ruInv_spec hg).2.1) harg es hesE hesC
    have hyH : vbK S l es ∈ cdHull S l :=
      kzKx hZρ hZρ1 hAt hKB hZ hZW (fun g hg => by
          obtain ⟨hc, hc2, -⟩ := ruInv_spec hg
          exact (ldHull_iff hl hX (hc2.trans (psi_lt hκ2 b))).2 hc)
        (fun d hd hdb => (harg d hd hdb).trans (hAeq ▸ hbA)) es hesE hesC
    have hesE' : RxEK S (vbW S l) K es := ⟨hesE.1.mono hZW, hesE.2⟩
    have hyb : vbK S l es < b := harg es hesE' hesT
    have hyD : VbDK S l K (vbK S l es) :=
      ⟨hyH, CSet_mono hbK.le (psi_mono hκ2 hbK.le).1 hyC, hyb.trans hbK⟩
    have hTy : vbTK S l K (vbK S l es) = es := vbTK_K hl hX hKB hesE'
    set y := vbK S l es with hydef
    set z := Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) with hzdef
    have hzb : z < b := hq y hyb
    have hpart : ∀ {c d : Ordinal.{0}}, y ∈ S.CSet c d →
        Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) ∈ S.CSet c d := fun hy => by
      have h := (Vh.vhC_div _ hy (Om (1 + 1 + 1))).1; rwa [h3e] at h
    have hzD : VbDK S l K z := ⟨CSet.add_mem (hpart hyD.1) (hO3 _ _),
      CSet.add_mem (hpart hyD.2.1) (hO3 _ _), hzb.trans hbK⟩
    have hzC : z ∈ S.CSet b (S.psi b (Om (1 + 1))) := CSet.add_mem (hpart hyC) (hO3 _ _)
    have hz3 : Om (1 + 1 + 1) ∣ z := dvd_add (dvd_mul_right _ _) (dvd_refl _)
    have hyz : y < z := by
      have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := h3SC.1.ne'
      conv_lhs => rw [← Ordinal.div_add_mod y (Om (1 + 1 + 1))]
      exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt y h30)
    obtain ⟨haD, han, ha3, hza, hψa⟩ := kzNorm hl hX hKB hzD (hAeq ▸ (hzb.trans hbA).le) hz3
    set a := S.M z (S.psi z (Om (1 + 1))) z with hadef
    have hψz : S.psi z (Om (1 + 1)) < S.psi b (Om (1 + 1)) := psi_lt_psi_of_mem hκ2 hzb hzC
    have hab : a < b := by
      by_contra hc
      push Not at hc
      exact absurd hψz (not_lt.2 (hψa ▸ (psi_mono hκ2 hc).1))
    have haN : KuNK S l K a := ⟨haD, han, ha3, (le_add_self : Om (1 + 1 + 1) ≤ z).trans hza⟩
    refine ⟨_, ⟨a, haN, hab, rfl⟩, ?_⟩
    have hesa : es < vbTK S l K a := hTy ▸ vbTK_mono hl hX hKB hyD haD (hyz.trans_le hza)
    rw [← hψes]
    exact psi_lt_psi_of_mem hκ2 hesa (CSet_mono hesa.le (psi_mono hκ2 hesa.le).1 hesn)
  refine kzLow hl hX hKB hA hρ hbD hbA fun ξ hξ hξP => ?_
  obtain ⟨y, ⟨a, haN, hab, rfl⟩, hξy⟩ :=
    kuDom (S := S) (M := α) (Z := Zb) (P := P) (𝒴 := 𝒴) hZ1 (psi_lt hκ2 _).le hne hSC hdir hsub ξ hξ hξP
  exact ⟨a, haN.1, psi_lt_psi_of_mem hκ2 hab (CSet_mono hab.le (psi_mono hκ2 hab.le).1 haN.2.1), hξy.le,
    IH a haN hab⟩

/-- **THE LAW AT `β' + Ω₃`**, `Ω₃ ∣ β'`, `β' ≠ 0`, from the law below. -/
theorem kzSucc {β' : Ordinal.{0}} (h3 : Om (1 + 1 + 1) ∣ β') (hβ0 : β' ≠ 0)
    (hb : KuNK S l K (β' + Om (1 + 1 + 1))) (hbA : β' + Om (1 + 1 + 1) < A)
    (IH : ∀ a, KuNK S l K a → a < β' + Om (1 + 1 + 1) → KuLawK S l K A a) :
    KuLawK S l K A (β' + Om (1 + 1 + 1)) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAeq : A = ConjT.Aη S (cdEta S l) := (Wg.wgOwnEta hl hX hA hρ).2
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := kx3SC.1.ne'
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this; rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by rw [Nat.cast_ofNat, one_add_one_eq_two]
  have h2K : Om (1 + 1 : Ordinal.{0}) < K :=
    (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0)).trans_le hKB.ge
  set b := β' + Om (1 + 1 + 1) with hbdef
  obtain ⟨hbD, hbn, -, -⟩ := hb
  have hβD : VbDK S l K β' := ⟨kxPred h3 hbD.1, kxPred h3 hbD.2.1, le_self_add.trans_lt hbD.2.2⟩
  have hβm : β' ∈ S.CSet b (S.psi b (Om (1 + 1))) := kxPred h3 hbn
  have hβn : β' ∈ S.CSet β' (S.psi β' (Om (1 + 1))) := by
    refine kwFUG (a₁ := β') (b := β' + Om (1 + 1 + 1)) (K := β') (fun {d e} he h1 h2 => ?_) hβm
    obtain ⟨q, hq⟩ := h3
    have h := (kwC_div e he (Om (1 + 1 + 1))).1
    rw [kx3e, kxDiv (hq ▸ h1) (hq ▸ h2), ← hq] at h
    exact h
  have hβ3 : Om (1 + 1 + 1) ≤ β' := by
    obtain ⟨q, rfl⟩ := h3
    have hq : q ≠ 0 := fun e => hβ0 (by rw [e, mul_zero])
    exact le_mul_left _ (pos_iff_ne_zero.2 hq)
  have hβb : β' < b := lt_add_of_pos_right _ (pos_iff_ne_zero.2 h30)
  have hlawβ : KuLawK S l K A β' := IH β' ⟨hβD, hβn, h3, hβ3⟩ hβb
  -- `T_K b = T_K β' + Ω₂`
  have h3D : VbDK S l K (Om (1 + 1 + 1)) := ⟨kxO3 _ _, kxO3 _ _, h3W.trans_le hKB.ge⟩
  have hT3 : vbTK S l K (Om (1 + 1 + 1)) = Om (1 + 1) := by
    have h := vbTK_Om hl hX hKB (S := S) (l := l) (k := 2) (by norm_num)
    rwa [e2] at h
  have hTb : vbTK S l K b = vbTK S l K β' + Om (1 + 1) := by
    rw [hbdef, kzT_add hl hX hKB hβD h3D, hT3]
  obtain ⟨hTβE, hTβK⟩ := vbTK_eq hl hX hKB hβD
  have hTβn := kzTr hl hX hKB hβD hβD hβn
  have hTβm : vbTK S l K β' % Om (1 + 1) = 0 := kzT_mod hl hX hKB β' hβD (Ordinal.mod_eq_zero_of_dvd h3)
  set Xb := S.psi (vbTK S l K β' + Om (1 + 1)) (Om (1 + 1)) with hXbdef
  have hXθ : Xb ≤ S.psi K (Om (1 + 1)) := (psi_mono hκ2 (hKB.sc.isPrincipal hTβE.2.2 h2K).le).1
  have hPX : S.psi (vbTK S l K b) (Om (1 + 1)) = Xb := by rw [hTb]
  set Zb := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZbdef
  have hZ : SC Zb := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZρ1.trans (psiS_bounds (S := S) _ 1).1)
  have hZ1 : Zb < Om 1 := kzZ_lt hl hX hKB hA hρ hbD hbA
  have hZW : Zb ≤ vbW S l := by rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 b).le
  have hω : ω ≤ S.psi (vbTK S l K β') (Om (1 + 1)) := (Lw.lw_omega_lt_SC (SC_psi hκ2 _)).le
  have hβat : S.psi β' (Om (1 + 1)) ∈ ldAtR S l := ⟨β', hβD.1, hAeq ▸ (hβb.trans hbA), rfl⟩
  refine kzLowG hl hX hKB hA hρ hbD hbA fun ξ hξ hξP => ?_
  rw [hPX] at hξP
  rcases le_or_gt ξ (S.psi (vbTK S l K β') (Om (1 + 1))) with hle | hgt
  · refine ⟨β', hβD, hβb.trans hbA, psi_lt_psi_of_mem hκ2 hβb hβm, ?_⟩
    rw [hlawβ]
    refine (psi_mono hκ1 ?_).1
    rw [add_assoc, one_add_of_omega0_le hω]
    exact add_le_add le_rfl hle
  · set ζ := ξ - S.psi (vbTK S l K β') (Om (1 + 1)) with hζdef
    have hξe : ξ = S.psi (vbTK S l K β') (Om (1 + 1)) + ζ := (Ordinal.add_sub_cancel_of_le hgt.le).symm
    have hζH := Kt.ktHCl_sub ξ hξ (S.psi (vbTK S l K β') (Om (1 + 1)))
    have hζX : ζ < Xb := (Ordinal.sub_le_self _ _).trans_lt hξP
    have hψK : S.psi K (Om (1 + 1)) < K := (psi_lt hκ2 K).trans h2K
    have hζE : RxEK S Zb K ζ :=
      ⟨rxN_of_HCl hZ1.le hζH, CSet.of_lt (hζX.trans_le hXθ), (hζX.trans_le hXθ).trans hψK⟩
    have hζEW : RxEK S (vbW S l) K ζ := ⟨hζE.1.mono hZW, hζE.2⟩
    have hLE : RxEK S (vbW S l) K (vbTK S l K β' + ζ) := kzE_add hKB hTβE hζEW
    have hκL : vbK S l (vbTK S l K β' + ζ) = β' + vbK S l ζ := by
      rw [kzK_add hl hX hKB _ hTβE _ hζEW, hTβK]
    have hκ3 : vbK S l ζ < Om (1 + 1 + 1) := by
      have h' := kzL_lt_lev hZρ hZρ1 hAt hKB ζ hζEW 1 (by rw [Nat.cast_one]; exact hζX.trans (psi_lt hκ2 _))
      rwa [Nat.cast_one] at h'
    have hab : β' + vbK S l ζ < b := (add_lt_add_iff_left β').2 hκ3
    have hcx : ∃ c, c ≤ vbTK S l K β' + ζ ∧ ζ ∈ S.CSet c (S.psi c (Om (1 + 1))) :=
      ⟨_, le_rfl, CSet.of_lt (xdLtPsi hTβn hTβm hζX)⟩
    have hκH : vbK S l ζ ∈ cdHull S l :=
      kzL_memL hZρ hZρ1 hAt hKB hZ hZW hLE ((le_of_eq hκL).trans (hAeq ▸ (hab.trans hbA)).le)
        (fun g hg => by
          obtain ⟨hc, hc2, -⟩ := ruInv_spec hg
          exact (ldHull_iff hl hX (hc2.trans (psi_lt hκ2 b))).2 hc) ζ hζE hcx
    have hκC : vbK S l ζ ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
      kzL_memL hZρ hZρ1 hAt hKB hZ hZW hLE ((le_of_eq hκL).trans hab.le)
        (fun g hg => CSet.of_lt (ruInv_spec hg).2.1) ζ hζE hcx
    have hbK : b < K := hbD.2.2
    have haD : VbDK S l K (β' + vbK S l ζ) :=
      ⟨CSet.add_mem hβD.1 hκH, CSet.add_mem hβD.2.1 (CSet_mono hbK.le (psi_mono hκ2 hbK.le).1 hκC),
        hab.trans hbK⟩
    have hψab : S.psi (β' + vbK S l ζ) (Om (1 + 1)) < S.psi b (Om (1 + 1)) :=
      psi_lt_psi_of_mem hκ2 hab (CSet.add_mem hβm hκC)
    have hlift := kzLiftK hl hX hKB (β := β') (Â := A + 1 + S.psi (vbTK S l K β') (Om (1 + 1))) (Xb := Xb)
      (fun ζ => vbTK S l K β' + ζ) hβat hlawβ.symm.le hXθ hβD.1
      (fun ζ _ _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hβn)
      (fun ζ hζ hζX' => ⟨kzE_add hKB hTβE hζ, by
        have hk : vbK S l (vbTK S l K β' + ζ) = vbK S l (vbTK S l K β') + vbK S l ζ :=
          kzK_add hl hX hKB _ hTβE ζ hζ
        exact (le_of_eq (hk.trans (by rw [hTβK]))),
        fun x hx => (xdLtPsi hTβn hTβm (hx.trans hζX')).trans_le (psi_mono hκ2 (add_le_add le_rfl hx.le)).1⟩)
    have h := hlift ζ hζEW hζX (hAeq ▸ (hab.trans hbA)) hκH
    refine ⟨β' + vbK S l ζ, haD, hab.trans hbA, hψab, ?_⟩
    have hsum : A + ξ = A + 1 + S.psi (vbTK S l K β') (Om (1 + 1)) + ζ := by
      rw [hξe, add_assoc A 1, one_add_of_omega0_le hω, add_assoc]
    rw [hsum]; exact h

/-- **THE TOP LAW AT EVERY `b ∈ KuNK` BELOW `A`.** -/
theorem kzTop : ∀ b, KuNK S l K b → b < A → KuLawK S l K A b := by
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := kx3SC.1.ne'
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by rw [Nat.cast_ofNat, one_add_one_eq_two]
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this; rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb hbA
  by_cases hq : ∀ y, y < b → Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) < b
  · exact kzLim hl hX hKB hA hρ hb hbA hq fun a ha hab => IH a hab ha (hab.trans hbA)
  · push Not at hq
    obtain ⟨y, hyb, hle⟩ := hq
    obtain ⟨q, hbq⟩ := hb.2.2.1
    have hlt : y / Om (1 + 1 + 1) < q := (Ordinal.lt_mul_iff_div_lt h30).1 (hbq ▸ hyb)
    have hle' : Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) ≤ b := by
      rw [hbq, ← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hlt) _
    have heq := le_antisymm hle' hle
    rw [← heq] at hb hbA ⊢
    rcases eq_or_ne (Om (1 + 1 + 1) * (y / Om (1 + 1 + 1))) 0 with h0 | h0
    · -- `b = Ω₃`: the law of `Kx.kxTop`
      rw [h0, zero_add]
      have hN : KuN S l (Om (1 + 1 + 1)) := ⟨⟨kxO3 _ _, kxO3 _ _, h3W⟩, kxO3 _ _, dvd_refl _, le_rfl⟩
      have h := kxTop hl hX hA hρ _ hN
      unfold KuLaw at h
      unfold KuLawK
      have hT : vbT S l (Om (1 + 1 + 1)) = Om (1 + 1) := by
        have h' := vbT_Om hl hX (S := S) (l := l) (k := 2) (by norm_num)
        rwa [e2] at h'
      have hTK : vbTK S l K (Om (1 + 1 + 1)) = Om (1 + 1) := by
        have h' := vbTK_Om hl hX hKB (S := S) (l := l) (k := 2) (by norm_num)
        rwa [e2] at h'
      rw [hT] at h; rw [hTK]; exact h
    · exact kzSucc hl hX hKB hA hρ (dvd_mul_right _ _) h0 hb hbA
        (fun a ha hab => IH a (heq ▸ hab) ha (hab.trans hbA))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kz
