import Googology.Trans.PoR.InaccPsi.R2.KwFU

/-!
# Kw: THE TOP LAW AT A LIMIT COEFFICIENT, from the law below

`Θ`, `T`, `D`, `A`, `W^x = leWe x` as before; `Ku.KuN`, `Ku.KuLaw`.  At `b = β + W^E·γ` (`W^{E+1} ∣ β`, `γ < Ω₂` a
limit code, `Ω₃ ≤ E`) every truncation `β + W^E·c` (`0 < c < γ` a code) is normal (`Kw.kwTrunc`: `c` is owned,
`Kt.ktOwnTw`, since `c < γ < ψ₂ b`), so it lies in `Ku.KuN` below `b` and has the law; `Kj.kjLim` gives the law at `b`.

* `kwSuffix` (**`β + W^E·c ∈ Ku.KuN`** for every code `0 < c < ψ₂ b`), `kwLimC` (**THE TOP LAW AT A LIMIT
  COEFFICIENT FROM THE LAW BELOW**: no hypothesis on `E`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ka Googology.Trans.PoR.InaccPsi.R2.Kj
  Googology.Trans.PoR.InaccPsi.R2.Kt Googology.Trans.PoR.InaccPsi.R2.Ku

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The truncations lie in the domain**: `β + W^E·c ∈ KuN` for every code `0 < c < ψ₂ b`, `b = β + W^E·γ`. -/
theorem kwSuffix {β E γ c : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hβD : VbD S l β) (hED : VbD S l E)
    (hγ0 : γ ≠ 0) (hγ2 : γ < Om (1 + 1)) (hE3 : Om (1 + 1 + 1) ≤ E) (hb : KuN S l (β + leWe E * γ))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hc0 : 0 < c) (hcb : c < S.psi (β + leWe E * γ) (Om (1 + 1))) :
    KuN S l (β + leWe E * c) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set b := β + leWe E * γ with hbdef
  obtain ⟨hbD, hbn, -, -⟩ := hb
  have hbθ : S.psi b (Om (1 + 1)) < ConjT.th S := psi_lt_psi_of_mem hκ2 hbD.2.2 hbD.2.1
  have hc2 : c < Om (1 + 1) := hcb.trans (psi_lt hκ2 _)
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hc2).2 hc
  have hcθ : c < ConjT.th S := hcb.trans hbθ
  have hE1W : E + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hED.2.2
  have hWE1 : leWe (E + 1) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE1W).1
  have hWc : leWe E * c < leWe (E + 1) := by
    rw [leWe_succ E]; exact mul_lt_mul_of_pos_left hc2 (leWe_pos E)
  have hWcD : VbD S l (leWe E * c) :=
    ⟨leMulWe_mem hED.1 hcH, leMulWe_mem hED.2.1 (CSet.of_lt hcθ), hWc.trans hWE1⟩
  -- `β` is normal
  have hlt1 : leWe E * γ < leWe (E + 1) := by
    rw [leWe_succ E]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
  have e1 : ∀ p, p = Om (1 + 1) * (E + 1) → ω ^ p * (b / ω ^ p) = β := by
    rintro p rfl
    obtain ⟨q, hq⟩ := hdv
    show leWe (E + 1) * (b / leWe (E + 1)) = β
    rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hlt1, add_zero]
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    rwa [e1 _ rfl] at h
  -- `c` is owned
  set t := KaT.base β (Om (1 + 1) * E) with htdef
  have hGv : ∀ v, t.ev v = β + leWe E * v := fun v => rfl
  have hown : c < S.psi (β + leWe E * c) (Om (1 + 1)) := by
    rw [← hGv]
    refine ktOwnTw t c (hcb.trans_le (psi_mono hκ2 ?_).1)
    rw [hGv, ← leWe_succ, hbdef]
    exact add_le_add le_rfl hlt1.le
  -- the divisibility
  have hW3 : leWe (Om (1 + 1 + 1)) = Om (1 + 1 + 1) := Vn.vnWe_Om3
  have hdv3E : Om (1 + 1 + 1) ∣ leWe E := by rw [← hW3]; exact leWe_dvd hE3
  have hdv3β : Om (1 + 1 + 1) ∣ β := (hdv3E.trans (leWe_dvd (le_of_lt (lt_add_one E)))).trans hdv
  refine ⟨⟨CSet.add_mem hβD.1 hWcD.1, CSet.add_mem hβD.2.1 hWcD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWcD.2.2⟩,
    kwTrunc hdv hγ0 hγ2 hbn hβn (Order.one_le_iff_pos.2 hc0) hown,
    dvd_add hdv3β (hdv3E.trans (dvd_mul_right _ _)), ?_⟩
  exact ((Ordinal.le_of_dvd (leWe_pos E).ne' hdv3E).trans (Ordinal.le_mul_left _ hc0)).trans le_add_self

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE TOP LAW AT A LIMIT COEFFICIENT FROM THE LAW BELOW.** -/
theorem kwLimC {β E γ : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hβD : VbD S l β) (hED : VbD S l E)
    (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγ2 : γ < Om (1 + 1)) (hlim : IsSuccLimit γ)
    (hE3 : Om (1 + 1 + 1) ≤ E) (hb : KuN S l (β + leWe E * γ))
    (IH : ∀ a, KuN S l a → a < β + leWe E * γ → KuLaw S l A a) :
    KuLaw S l A (β + leWe E * γ) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hγ0 : γ ≠ 0 := hlim.ne_bot
  have hγm := (kjEfrom hdv hγ0 hγ2 hb.2.1).2
  have hγb : γ < S.psi (β + leWe E * γ) (Om (1 + 1)) := lt_psi_of_mem hκ2 hγm hγ2
  have hbθ : S.psi (β + leWe E * γ) (Om (1 + 1)) < ConjT.th S := psi_lt_psi_of_mem hκ2 hb.1.2.2 hb.1.2.1
  refine kjLim hl hX hA hρ hβD hED hγc (hγb.trans hbθ) hlim fun c hc hc0 hcγ => IH _ ?_ ?_
  · exact kwSuffix hl hX hdv hβD hED hγ0 hγ2 hE3 hb hc hc0 (hcγ.trans hγb)
  · exact (add_lt_add_iff_left β).2 (mul_lt_mul_of_pos_left hcγ (leWe_pos E))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kw

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kw.kwSuffix
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kw.kwLimC
