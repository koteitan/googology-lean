import Googology.Trans.PoR.InaccPsi.R2.YgK

/-!
# `YbIF` below `B₂`: every code is in the inacc-free closure

`Ω₁ = Om 1`, `Ω₂ = Om (1 + 1)`, `ψ = S.psi · Ω₂`, `UcCl q` the codes over `q` below `B₂ = Uc.ucB`, `TlCl q` the codes
below `X = Tl.tlX`, `YgK S q` the inacc-free closure without fixed atoms (`Yg.YgK`).  The proofs of `Uo.uo_tlK` and
`Uo.uo_ucK` (which put the codes into `Ul.UlK`, a closure WITH the inaccessibles) use the inversion `Uo.uoArg` (the
own argument of a collapse in `K_q` is in `K_q`), which has no inacc-free version.  Here the own argument is carried
along the induction instead:

* `YgOwnK S q x` (**every own argument `B` with `ψ(B) = x` is in `YgK S q`**), `ygOwn_vac` (vacuous unless `x` is a
  strongly critical point above `Ω₁`), `ygOwn_eq` (from one own argument in `YgK`, by `Ts.ts_own_unique`);
* `ygTlK` (**`TlCl q ⊆ YgK S q`, with the own arguments**), `ygUcK` (**`UcCl q ⊆ YgK S q`, with the own
  arguments**), for a strongly critical `q ≤ Ω₁`;
* `ygIF_lowB` (**`YbIF` below `B₂`**: `Ω₁ ≤ M < B₂`, `ucDat M < q` (`q` strongly critical, `q ≤ Ω₁`) ⇒ `M ∈ YbK S q`),
  `YgIFTh` (the part of `Yb.YbIF` left: levels `B₂ ≤ M < θ`), `ygIF_of_th` (**`YgIFTh S ⇒ Yb.YbIF S`**).

No new axiom.  New definitions: `YgOwnK`, `YgIFTh` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Uf
  Googology.Trans.PoR.InaccPsi.R2.Tw

variable {S : InaccSeq.{0}}

/-- **Every own argument of a collapse equal to `x` is in `YgK S q`.** -/
def YgOwnK (S : InaccSeq.{0}) (q x : Ordinal.{0}) : Prop :=
  ∀ B, B ∈ S.CSet B (S.psi B (Om (1 + 1))) → S.psi B (Om (1 + 1)) = x → YgK S q B

theorem ygOwn_vac {q x : Ordinal.{0}} (h : ¬ (SC x ∧ Om 1 < x)) : YgOwnK S q x := fun B _ e =>
  absurd ⟨e ▸ SC_psi (InR_Om_succ 1) B, e ▸ ts_Om1_lt_psi B⟩ h

theorem ygOwn_eq {q e x : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (hx : S.psi e (Om (1 + 1)) = x) (he : YgK S q e) : YgOwnK S q x := fun B hB e' => by
  rw [ts_own_unique hB hown (e'.trans hx.symm)]; exact he

theorem yg_notSC_veblen {x a b : Ordinal.{0}} (ha : a < x) (hb : b < x) (e : veblen a b = x) :
    ¬ (SC x ∧ Om 1 < x) := fun h => SC.not_veblen_lt h.1 ha hb e

theorem yg_notSC_notE {x : Ordinal.{0}} (hE : ¬ ω ^ x = x) : ¬ (SC x ∧ Om 1 < x) := fun h =>
  hE (Low.opow_eq_self_of_SC h.1)

/-- **`TlCl Z ⊆ YgK S Z`, with the own arguments** (`Z` strongly critical, `Z ≤ Ω₁`). -/
theorem ygTlK {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) :
    ∀ x, TlCl Z x → YgK S Z x ∧ YgOwnK S Z x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases lt_trichotomy x Om1 with h | h | h
  · refine ⟨YgK.small (hx.lt_of_lt_Om1 hZS h), ygOwn_vac fun hs => ?_⟩
    rw [← tw_Om1_eq] at hs; exact absurd (hs.2.trans h) (lt_irrefl _)
  · subst h
    refine ⟨by rw [tw_Om1_eq]; exact ygW1, ygOwn_vac fun hs => ?_⟩
    rw [← tw_Om1_eq] at hs; exact lt_irrefl _ hs.2
  have hzX := tw_cl_lt hZ hx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := tl_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      refine ⟨?_, ygOwn_vac (yg_notSC_veblen hI h2l e)⟩
      rw [← e]
      exact YgK.phi (IH _ hI h1).1 (IH _ h2l h2).1
    · have hSC := tl_SC_of h hI
      obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h hzX
      obtain ⟨hcβ, hcy⟩ := tl_cl_atom hZ x hx hSC h
      generalize hβdef : tlLev x = β at hnf hyz hlz hcβ hcy
      generalize hydef : tlI β x = y at hnf hyz hcy
      have hβX : β < tlX := hlz.trans hzX
      have h1' : Om 1 < rhF β y := by rw [hnf, ← tw_Om1_eq]; exact h
      have hyz' : y < rhF β y := by rw [hnf]; exact hyz
      have hzX' : rhF β y < tlX := by rw [hnf]; exact hzX
      obtain ⟨B, c, D, hown, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        twRun (S := S) hZS hZ hcy hβX hyz' h1' hzX'
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      have hβz : β < rhF β (c + D) := by rw [hcD, hnf]; exact hlz
      obtain ⟨hψe, hown'⟩ := twRun_eq hown hdvd hc hD2 hval hβz
      rw [hcD, hnf] at hψe
      have hβC := (IH β hlz hcβ).1
      have hDC := (IH D hDz hDc).1
      have hBC : YgK S Z B := by
        rcases hcase with ⟨-, hB0, -⟩ | ⟨-, hBw, -⟩ | ⟨-, hcf, -⟩
        · rw [hB0]; exact YgK.zero
        · rw [hBw]; exact ygLeWe hZS hβC
        · have hψc : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          exact (IH c hcz hcc).2 B hown hψc
      have heK : YgK S Z (B + leWe β * D) := YgK.add hBC (ygLeMulWe hZS hβC hDC)
      refine ⟨?_, ygOwn_eq hown' hψe heK⟩
      rw [← hψe]
      exact ygPsi2 heK
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tlDec hZS x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : TlCl Z (ω ^ g * k) := TlCl.mul_nat hZS.1 (TlCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := (IH _ hgl hlog).1
    have hmC := (IH _ hml hr).1
    refine ⟨?_, ygOwn_vac (yg_notSC_notE hE)⟩
    rw [← hdec]
    exact YgK.add ((YgK.opow hgC).mul_nat k) hmC

/-- **`UcCl Z ⊆ YgK S Z`, with the own arguments** (`Z` strongly critical, `Z ≤ Ω₁`). -/
theorem ygUcK {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) :
    ∀ x, UcCl Z x → YgK S Z x ∧ YgOwnK S Z x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hxB := uf_cl_lt_B hZ hx
  rcases lt_or_ge x tlX with hxX | hXx
  · exact ygTlK hZS hZ x (uc_cl_lt_X hx hxX)
  have h : Om1 < x := uc_Om1_lt_of_X hXx
  by_cases hE : ω ^ x = x
  · by_cases hI : invVeblen₁ x < x
    · obtain ⟨h1, h2⟩ := uc_cl_inv hZ x hx h hE hI
      have h2l := Tf.tf_inv2_lt hE
      have e : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      refine ⟨?_, ygOwn_vac (yg_notSC_veblen hI h2l e)⟩
      rw [← e]
      exact YgK.phi (IH _ hI h1).1 (IH _ h2l h2).1
    · have hSC := tl_SC_of h hI
      have hne := uc_nf_of_lt hSC h hxB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h hne
      obtain ⟨hcl, hcy⟩ := uc_cl_atom hZ x hx hSC hXx hxB
      generalize hldef : ucLev x = l at hlE hlv hnf hyz hcl hcy
      generalize hydef : ucI l x = y at hnf hyz hcy
      obtain ⟨B, c, D, hown, hBE, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        ufRun (S := S) hZS hZ hlE hcy (by rw [hnf]; exact hyz) (by rw [hnf]; exact hxB)
      have hcz : c < x := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < x := (le_add_self.trans_eq hcD).trans_lt hyz
      obtain ⟨hψe, -, hown', -⟩ := ufRun_eq hlE hown hBE hdvd hc hD2 hval
      rw [hcD, hnf] at hψe
      have hlC : YgK S Z l := yg_K_comps hZS l hlE fun c' hc' =>
        (IH c' ((le_ucC hc').trans_lt hlv) (hcl c' hc')).1
      have hDC := (IH D hDz hDc).1
      have hBC : YgK S Z B := by
        rcases hcase with hc0 | ⟨-, hcf, -, -⟩
        · subst hc0
          rcases eq_or_ne l 0 with hl0 | hl0
          · subst hl0
            have hψ : S.psi B (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := by rw [← hc, uf_H0]
            rw [Ts.ts_own_unique hown (CSet.zero_mem _ _) hψ]; exact YgK.zero
          have h0B : ucH l 0 < ucB := ((uf_H_le_iff l).2 zero_le).trans_lt (by rw [hnf]; exact hxB)
          obtain ⟨K, hownK, -, hBK, -, hK⟩ :=
            uf_first_base (S := S) (Order.one_le_iff_ne_zero.2 hl0) hlE h0B hown hc
          have hWl : YgK S Z (OmTwo ^ l) := by
            have := ygLeWe hZS hlC; rwa [uc_leWe] at this
          rw [hBK]
          refine YgK.add ?_ hWl
          rcases hK with ⟨hK0, -⟩ | ⟨hKm, -, hmaxK⟩
          · rw [hK0]; exact YgK.zero
          · have hmc : ucC l ∈ ucComps l := uf_ucC_mem l hlE
            have hvS : SC (S.psi K (Om (1 + 1))) := Ts.ts_psi_SC K
            have hv1 : Om1 < S.psi K (Om (1 + 1)) := by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi K
            obtain ⟨t, htc, htS, hvt, htm⟩ := uf_SC_code hZ _ (hcl _ hmc) _ hvS hv1 hKm
            have htv : t = S.psi K (Om (1 + 1)) := le_antisymm (hmaxK t htS (hv1.trans_le hvt) htm) hvt
            rw [htv] at htc
            exact (IH _ (hKm.trans_lt hlv) htc).2 K hownK rfl
        · have hψc : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          exact (IH c hcz hcc).2 B hown hψc
      have hWD : YgK S Z (OmTwo ^ l * D) := by
        have := ygLeMulWe hZS hlC hDC; rwa [uc_leWe] at this
      have heK : YgK S Z (B + OmTwo ^ l * D) := YgK.add hBC hWD
      refine ⟨?_, ygOwn_eq hown' hψe heK⟩
      rw [← hψe]
      exact ygPsi2 heK
  · have hz0 : x ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ucDec hZS hZ x hx
    set g := log ω x with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hdec : ω ^ g * k + x % ω ^ g = x := by
      have := Ordinal.div_add_mod x (ω ^ g); rwa [hk] at this
    have hwk : UcCl Z (ω ^ g * k) := UcCl.mul_nat hZS.1 (UcCl.opow hZS.1 hlog) k
    have hle : ω ^ g * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl Z (x % ω ^ g) := by
      have e : x - ω ^ g * k = x % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hgl := Tf.tf_log_lt h hE
    have hml := Rj.rj_mod_lt hz0
    have hgC := (IH _ hgl hlog).1
    have hmC := (IH _ hml hr).1
    refine ⟨?_, ygOwn_vac (yg_notSC_notE hE)⟩
    rw [← hdec]
    exact YgK.add ((YgK.opow hgC).mul_nat k) hmC

/-! ## `YbIF` below `B₂` -/

/-- **`YbIF` below `B₂`**: every level `M < B₂` with `ucDat M < q` (`q` strongly critical, `q ≤ Ω₁`) is in the
inacc-free closure `YbK S q`. -/
theorem ygIF_lowB {M q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hMB : M < ucB) (hd : ucDat M < q) :
    Yb.YbK S q M :=
  ((ygUcK (S := S) hq hq1 M ((uc_cl_iff hq hMB).2 hd)).1).toYb hq.1

/-- **The part of `Yb.YbIF` left**: the levels `B₂ ≤ M < θ`. -/
def YgIFTh (S : InaccSeq.{0}) : Prop :=
  ∀ M q : Ordinal.{0}, ucB ≤ M → M < ConjT.th S → SC q → q ≤ Om1 → Vd.vdD S 0 M < q → Yb.YbK S q M

/-- **`YgIFTh S ⇒ Yb.YbIF S`.** -/
theorem ygIF_of_th (H : YgIFTh S) : Yb.YbIF S := by
  intro M q _ hMθ hq hq1 h1 h2
  rcases lt_or_ge M ucB with hMB | hMB
  · exact ygIF_lowB hq hq1 hMB (h1 hMB)
  · exact H M q hMB hMθ hq hq1 (h2 hMB)

end Googology.Trans.PoR.InaccPsi.R2.Yg
