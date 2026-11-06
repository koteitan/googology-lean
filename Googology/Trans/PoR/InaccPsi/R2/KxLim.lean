import Googology.Trans.PoR.InaccPsi.R2.KxInv

/-!
# Kx: THE TOP LAW AT EVERY `b` WHOSE `Ω₃`-QUOTIENT IS A LIMIT, from the law below

`Θ`, `T`, `D`, `A`, `κ = Vb.vbK` as before; `Ku.KuN`, `Ku.KuLaw`; `Z = Θ(ψ₂ b)`, `P = ψ₂(T b)`, `α_b = A + 1 + P`.
Let `b ∈ KuN` with `Ω₃·(y/Ω₃) + Ω₃ < b` for every `y < b` (the quotient `b/Ω₃` is a limit).  By `Ks.ksLow` and
`Ku.kuDom` (the family `𝒴 = {ψ₂(T a) : a ∈ KuN, a < b}`, directed) it suffices to dominate every atom
`ψ₂(e) < P`, `e ∈ HCl(α_b, Z)`:

* `e* = M(e)` (the normal argument: `ψ₂ e* = ψ₂ e`, `e* ∈ HCl(α_b, Z)`, `e* < T b`, `e* ∈ Cl(T b, P)`);
* `y = κ e* ∈ Cl(b, ψ₂ b)` (`Kx.kxK`: the countable parts of `e*` are below `Z`, its arguments below `T b`), so
  `y ∈ D`, `T y = e*`, `y < b`;
* `z = Ω₃·(y/Ω₃) + Ω₃ < b`, `z ∈ Cl(b, ψ₂ b)`, so `ψ₂ z < ψ₂ b`; `a = M(z)` (`Kx.kxNorm`) is in `KuN`, `a < b`, and
  `e* < T a`, so `ψ₂(e) = ψ₂(e*) < ψ₂(T a)`.

* `kxLim` (**THE TOP LAW AT EVERY LIMIT `Ω₃`-QUOTIENT FROM THE LAW BELOW**: no classification of `b`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Vb
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ku
  Googology.Trans.PoR.InaccPsi.R2.Ks

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE TOP LAW AT EVERY LIMIT `Ω₃`-QUOTIENT FROM THE LAW BELOW.** -/
theorem kxLim {b : Ordinal.{0}} (hb : KuN S l b)
    (hq : ∀ y, y < b → Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) < b)
    (IH : ∀ a, KuN S l a → a < b → KuLaw S l A a) : KuLaw S l A b := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨hbD, hbn, -, hb3le⟩ := hb
  set Zb := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZbdef
  set P := S.psi (vbT S l b) (Om (1 + 1)) with hPdef
  set α := A + 1 + P with hαdef
  have hZ : SC Zb := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZρ1.trans (psiS_bounds (S := S) _ 1).1)
  have hZ1 : Zb < Om 1 := kuZ_lt hl hX hA hρ hbD
  have hZL : Zb ≤ S.Lam := (hZ1.trans (Om_lt_Om.2 (lt_add_one 1))).le.trans Xd.xdOm2_le_Lam
  have hZW : Zb ≤ vbW S l := by rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 b).le
  have hbW : b < Om ω := hbD.2.2
  have hAω : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  have hO3 : ∀ x y : Ordinal.{0}, Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet x y := fun x y =>
    CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem x y)))
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this; rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  have h3SC : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne'
  have h3e : ω ^ Om (1 + 1 + 1 : Ordinal.{0}) = Om (1 + 1 + 1) := gg_SC_eps h3SC
  obtain ⟨hTbE, hTbK⟩ := vbT_eq hl hX hbD
  -- the members `a` of the domain below `b` and their images
  set 𝒴 : Set Ordinal.{0} := {y | ∃ a, KuN S l a ∧ a < b ∧ y = S.psi (vbT S l a) (Om (1 + 1))} with h𝒴
  have h3N : KuN S l (Om (1 + 1 + 1)) :=
    ⟨⟨hO3 _ _, hO3 _ _, h3W⟩, hO3 _ _, dvd_refl _, le_rfl⟩
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
    · exact ⟨_, ⟨a₂, h2N, h2b, rfl⟩, (psi_mono hκ2 ((vbT_le_iff hl hX h1N.1 h2N.1).1 h)).1, le_rfl⟩
    · exact ⟨_, ⟨a₁, h1N, h1b, rfl⟩, le_rfl, (psi_mono hκ2 ((vbT_le_iff hl hX h2N.1 h1N.1).1 h)).1⟩
  -- the atoms
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
    have hesT : es < vbT S l b := by
      by_contra hc
      push Not at hc
      exact absurd hψe (not_lt.2 (hψes ▸ (psi_mono hκ2 hc).1))
    have hTbW : vbT S l b < Om ω := (vbT_mem hl hX hbD).2
    have hesW : es < Om ω := hesT.trans hTbW
    have hesE : RxE S Zb es :=
      ⟨rxN_of_HCl hZ1.le hesH, CSet_mono hesW.le (psi_mono hκ2 hesW.le).1 hesn, hesW⟩
    have hesC : es ∈ S.CSet (vbT S l b) P := CSet_mono hesT.le (psi_mono hκ2 hesT.le).1 hesn
    -- `y = κ e*` in `Cl(b, ψ₂ b)` and in the hull
    have harg : ∀ d, RxE S (rxW (upsilon l) (ldAtR S l)) d → d < vbT S l b →
        rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) d < b := fun d hd hdb => by
      have h := vbK_mono hl hX hd hTbE hdb
      rwa [hTbK] at h
    have hyC : vbK S l es ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
      kxK hZρ hZρ1 hAt hZ hZW (fun g hg => CSet.of_lt (ruInv_spec hg).2.1) harg es hesE hesC
    have hyH : vbK S l es ∈ cdHull S l :=
      kxK hZρ hZρ1 hAt hZ hZW (fun g hg => by
          obtain ⟨hc, hc2, -⟩ := ruInv_spec hg
          exact (ldHull_iff hl hX (hc2.trans (psi_lt hκ2 b))).2 hc)
        (fun d hd hdb => (harg d hd hdb).trans (hbW.trans_le hAω)) es hesE hesC
    have hesE' : RxE S (vbW S l) es := hesE.mono hZW
    have hyb : vbK S l es < b := harg es hesE' hesT
    have hyD : VbD S l (vbK S l es) :=
      ⟨hyH, CSet_mono hbW.le (psi_mono hκ2 hbW.le).1 hyC, hyb.trans hbW⟩
    have hTy : vbT S l (vbK S l es) = es := vbT_K hl hX hesE'
    set y := vbK S l es with hydef
    -- `z = Ω₃·(y/Ω₃) + Ω₃`
    set z := Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) + Om (1 + 1 + 1) with hzdef
    have hzb : z < b := hq y hyb
    have hpart : ∀ {c d : Ordinal.{0}}, y ∈ S.CSet c d →
        Om (1 + 1 + 1) * (y / Om (1 + 1 + 1)) ∈ S.CSet c d := fun hy => by
      have h := (Vh.vhC_div _ hy (Om (1 + 1 + 1))).1; rwa [h3e] at h
    have hzD : VbD S l z := ⟨CSet.add_mem (hpart hyD.1) (hO3 _ _), CSet.add_mem (hpart hyD.2.1) (hO3 _ _),
      hzb.trans hbW⟩
    have hzC : z ∈ S.CSet b (S.psi b (Om (1 + 1))) := CSet.add_mem (hpart hyC) (hO3 _ _)
    have hz3 : Om (1 + 1 + 1) ∣ z := dvd_add (dvd_mul_right _ _) (dvd_refl _)
    have hyz : y < z := by
      have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := h3SC.1.ne'
      conv_lhs => rw [← Ordinal.div_add_mod y (Om (1 + 1 + 1))]
      exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt y h30)
    -- `a = M(z)`
    obtain ⟨haD, han, ha3, hza, hψa⟩ := kxNorm hl hX hzD hz3
    set a := S.M z (S.psi z (Om (1 + 1))) z with hadef
    have hψz : S.psi z (Om (1 + 1)) < S.psi b (Om (1 + 1)) := psi_lt_psi_of_mem hκ2 hzb hzC
    have hab : a < b := by
      by_contra hc
      push Not at hc
      exact absurd hψz (not_lt.2 (hψa ▸ (psi_mono hκ2 hc).1))
    have haN : KuN S l a := ⟨haD, han, ha3, (le_add_self : Om (1 + 1 + 1) ≤ z).trans hza⟩
    refine ⟨_, ⟨a, haN, hab, rfl⟩, ?_⟩
    have hesa : es < vbT S l a := hTy ▸ vbT_mono hl hX hyD haD (hyz.trans_le hza)
    rw [← hψes]
    exact psi_lt_psi_of_mem hκ2 hesa (CSet_mono hesa.le (psi_mono hκ2 hesa.le).1 hesn)
  refine ksLow hl hX hA hρ hbD fun ξ hξ hξP => ?_
  obtain ⟨y, ⟨a, haN, hab, rfl⟩, hξy⟩ :=
    kuDom (S := S) (M := α) (Z := Zb) (P := P) (𝒴 := 𝒴) hZ1 (psi_lt hκ2 _).le hne hSC hdir hsub ξ hξ hξP
  refine ⟨a, haN.1, psi_lt_psi_of_mem hκ2 hab (CSet_mono hab.le (psi_mono hκ2 hab.le).1 haN.2.1), hξy.le,
    IH a haN hab⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kx.kxLim
