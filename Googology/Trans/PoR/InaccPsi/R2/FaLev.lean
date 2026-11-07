import Googology.Trans.PoR.InaccPsi.R2.FaShape
import Googology.Trans.PoR.InaccPsi.R2.YvLev
import Googology.Trans.PoR.InaccPsi.R2.QcFr

/-!
# Fa: THE LEAF SUBSTITUTION COMMUTES WITH `T`

`T = Kz.vbTK S λ K`, `T' = Kz.vbTK S λ' K`, `Θ`, `Θ'` the readings at `λ`, `λ'`.  `FaGood u`: `u = Θ c` for a code `c` of `λ` with `Ψ u = Θ' c`.

* `fa_X` (**`T(ψ₃(Ω₃^{Ω₃})) = X`**), `fa_ucMap` (**`ucMap f (T w) = T' w`**, base-`Ω₂` normal forms below `E₂`);
* `faLevLow` (**`vcSub Ψ (T x) = T' x`** below `B₂`, every leaf good), `faLevR` (**`YvR Ψ (T x) (T' x)`**: every leaf of `T x` good),
  `faLevSub` (**`yvSub Ψ (T x) = T' x`**).

No new axiom.  New definition: `FaGood`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- A leaf whose image is the reading of the same code at `λ'`. -/
def FaGood (S : InaccSeq.{0}) (l l' : Ordinal.{0}) (Ψ : Ordinal.{0} → Ordinal.{0}) (u : Ordinal.{0}) : Prop :=
  ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ gxTh (upsilon l) (ldAtR S l) c = u ∧ Ψ u = gxTh (upsilon l') (ldAtR S l') c

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

theorem fa_O2_D (hKB : KzB S K) : VbDK S l K (Om (1 + 1 : Ordinal.{0})) := by
  have := fa_Om1_D (S := S) (l := l) hKB 1; simpa using this

include hl hX hKB

theorem fa_T_O2 : vbTK S l K (Om (1 + 1)) = Om 1 := by
  have h := vbTK_Om (S := S) hl hX hKB (k := 1) le_rfl
  simpa using h

theorem fa_T_O3 : vbTK S l K (Om (1 + 1 + 1)) = Om (1 + 1) := by
  have h := vbTK_Om (S := S) hl hX hKB (k := 2) (by omega)
  have e : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
  rwa [e] at h

theorem fa_lt_O2 {x : Ordinal.{0}} (hx : VbDK S l K x) (h : vbTK S l K x < Om 1) : x < Om (1 + 1) :=
  not_le.1 fun hc => absurd h (not_lt.2 (by simpa using vbTK_ge_lev hl hX hKB hx 0 (by simpa using hc)))

theorem fa_lt_O3 {x : Ordinal.{0}} (hx : VbDK S l K x) (h : vbTK S l K x < Om (1 + 1)) : x < Om (1 + 1 + 1) :=
  not_le.1 fun hc => absurd h (not_lt.2 (by simpa using vbTK_ge_lev hl hX hKB hx 1 (by simpa using hc)))

theorem fa_T_lt_O1 {x : Ordinal.{0}} (hx : VbDK S l K x) (h : x < Om (1 + 1)) : vbTK S l K x < Om 1 := by
  have := vbTK_lt_lev hl hX hKB hx 0 (by simpa using h)
  simpa using this

theorem fa_T_lt_O2 {x : Ordinal.{0}} (hx : VbDK S l K x) (h : x < Om (1 + 1 + 1)) : vbTK S l K x < Om (1 + 1) := by
  have := vbTK_lt_lev hl hX hKB hx 1 (by simpa using h)
  simpa using this

/-- **`T(ψ₃(Ω₃^{Ω₃})) = X`**, and the code is in `D_K`. -/
theorem fa_X (hAW : Om ω ≤ ConjT.Aη S (cdEta S l)) :
    VbDK S l K (S.psi (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) (Om (1 + 1 + 1))) ∧
      vbTK S l K (S.psi (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) (Om (1 + 1 + 1))) = tlX := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have h3 := fa_O3_D (S := S) (l := l) hKB
  have hd : VbDK S l K (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) := by
    rw [Ui.ui_W_eq (1 + 1)]
    have h1 := hPC.opow_mul h3 _ h3
    rw [fa_3e] at h1
    exact hPC.opow h1
  have hs : (1 + 1 : Ordinal.{0}) < ω := Ui.ui_s1_lt_omega one_lt_omega0
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hOW : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  have hdW : Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := by
    rw [Ui.ui_W_eq (1 + 1)]
    have hmul : IsPrincipal (· * ·) (Om ω : Ordinal.{0}) := by
      have h := isPrincipal_mul_omega0_opow_opow (Om ω : Ordinal.{0})
      rwa [gg_SC_eps hOW, gg_SC_eps hOW] at h
    have h1 : Om (1 + 1 + 1) * Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := hmul h3W h3W
    have := (isNormal_opow one_lt_omega0).strictMono h1
    rwa [gg_SC_eps hOW] at this
  have hown : Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0}) ∈
      S.CSet (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0}))
        (S.psi (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) (Om (1 + 1 + 1))) := by
    have h : ∀ a b, Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => by
      have h := Ul.ul_Wpow_mem (S := S) hs (Kx.kxO3 (S := S) a b) (CSet.one_mem a b)
      rwa [mul_one] at h
    exact h _ _
  have hD := fa_coll (S := S) (l := l) hKB (j := 2) hd (hdW.trans_le hAW)
  have e2 : ((2 : ℕ) : Ordinal.{0}) + 1 = 1 + 1 + 1 := by norm_num
  rw [e2] at hD
  refine ⟨hD, ?_⟩
  have hat := (vbTK_atom hl hX hKB (k := 1) le_rfl hd (by simpa using hown)).1
  simp only [Nat.cast_one] at hat
  rw [hat]
  have hTd : vbTK S l K (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) = Om (1 + 1) ^ Om (1 + 1 : Ordinal.{0}) := by
    have h := faT_Wmul hl hX hKB (k := 1) h3 hPC.one
    simp only [Nat.cast_one, mul_one] at h
    rw [h, fa_T_O3 hl hX hKB, fa_T_one hl hX hKB, mul_one]
  rw [hTd]
  have h := Ts.ts_psiW_eq_X (S := S)
  have e3 : Le.leWe (Om (1 + 1 : Ordinal.{0})) = Om (1 + 1) ^ Om (1 + 1 : Ordinal.{0}) := by
    rw [Ui.ui_W_eq 1]; rfl
  rwa [e3] at h

end Rst

section Two

variable {l l' ηx ηx' K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx') (hKB : KzB S K)

include hl hX hl' hX' hKB

/-- **`ucMap f (T w) = T' w`.** -/
theorem fa_ucMap {f : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}}
    (hf : ∀ w, VbDK S l K w → VbDK S l' K w → vbTK S l K w < Om (1 + 1) → vbTK S l K w ∈ A →
      f (vbTK S l K w) = vbTK S l' K w) :
    ∀ u, u < ucE → ∀ w, VbDK S l K w → VbDK S l' K w → vbTK S l K w = u → (∀ v ∈ ucComps u, v ∈ A) →
      ucMap f u = vbTK S l' K w ∧ vbTK S l' K w < ucE := by
  have hO2 : (OmTwo : Ordinal.{0}) = Om (1 + 1) := Uc.uc_Om2_eq
  have hPC := faPC_D (S := S) (l := l) hKB
  have hPC' := faPC_D (S := S) (l := l') hKB
  have h3 := fa_O3_D (S := S) (l := l) hKB
  have h3' := fa_O3_D (S := S) (l := l') hKB
  intro u
  induction u using WellFoundedLT.induction with
  | ind u IH =>
  intro huE w hw hw' hTw hA
  by_cases hu2 : u < OmTwo
  · have hTw2 : vbTK S l K w < Om (1 + 1) := by rw [hTw, ← hO2]; exact hu2
    have hw3 := fa_lt_O3 hl hX hKB hw hTw2
    have hT' := fa_T_lt_O2 hl' hX' hKB hw' hw3
    rw [ucMap_small f hu2, ← hTw]
    refine ⟨hf w hw hw' hTw2 (hA _ ?_), hT'.trans (by rw [← hO2]; exact ucE_gt)⟩
    rw [hTw, ucComps_small hu2]; rfl
  have hu2' : OmTwo ≤ u := not_lt.1 hu2
  have hw3 : Om (1 + 1 + 1) ≤ w := not_lt.1 fun hc => by
    have := fa_T_lt_O2 hl hX hKB hw hc
    rw [hTw, ← hO2] at this
    exact hu2 this
  have h1W : (1 : Ordinal.{0}) < Om (1 + 1 + 1) := Ui.ui_one_lt_SC (Ui.ui_SC_W _)
  have hw0 : w ≠ 0 := ((Kx.kx3SC.1).trans_le hw3).ne'
  set e := Ordinal.log (Om (1 + 1 + 1)) w with hedef
  set d := w / Om (1 + 1 + 1) ^ e with hddef
  set r := w % Om (1 + 1 + 1) ^ e with hrdef
  have hWe0 : Om (1 + 1 + 1) ^ e ≠ 0 := (Ui.ui_W_pos _ e).ne'
  have hdec : Om (1 + 1 + 1) ^ e * d + r = w := Ordinal.div_add_mod w _
  have hd3 : d < Om (1 + 1 + 1) := div_opow_log_lt w h1W
  have hd0 : d ≠ 0 := ((Ordinal.div_pos hWe0).2 (opow_log_le_self _ hw0)).ne'
  have hrlt : r < Om (1 + 1 + 1) ^ e := Ordinal.mod_lt w hWe0
  have he1 : (1 : Ordinal.{0}) ≤ e := le_log_of_opow_le h1W (by rw [opow_one]; exact hw3)
  have hdig : w / Om (1 + 1 + 1) ^ e % Om (1 + 1 + 1) ≠ 0 := by
    show d % Om (1 + 1 + 1) ≠ 0
    rwa [Ordinal.mod_eq_of_lt hd3]
  have hparts : ∀ {P : Ordinal.{0} → Prop}, FaPC P → P (Om (1 + 1 + 1)) → P w →
      P e ∧ P d ∧ P r ∧ P (Om (1 + 1 + 1) ^ e) ∧ P (Om (1 + 1 + 1) ^ e * d) := fun {P} hP hP3 hPw => by
    have hPe := hP.dig_exp (r := 1 + 1) hP3 hPw e hdig
    have hPm : P (Om (1 + 1 + 1) * e) := by
      have := hP.opow_mul hP3 e hPe; rwa [Ui.ui_W_opow (1 + 1)] at this
    have hPd : P d := by
      show P (w / Om (1 + 1 + 1) ^ e)
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.div w hPw _ hPm
    have hPr : P r := by
      show P (w % Om (1 + 1 + 1) ^ e)
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.mod w hPw _
    have hPW : P (Om (1 + 1 + 1) ^ e) := by
      rw [Ui.ui_W_eq (1 + 1) e]
      have := hP.opow_mul hPm _ hP.one
      rwa [mul_one] at this
    have hPWd : P (Om (1 + 1 + 1) ^ e * d) := by
      rw [Ui.ui_W_eq (1 + 1) e]; exact hP.opow_mul hPm _ hPd
    exact ⟨hPe, hPd, hPr, hPW, hPWd⟩
  obtain ⟨heD, hdD, hrD, hWeD, hWdD⟩ := hparts hPC h3 hw
  obtain ⟨heD', hdD', hrD', hWeD', hWdD'⟩ := hparts hPC' h3' hw'
  have hWmul : ∀ {l₀ : Ordinal.{0}} {ηy : Ordinal.{0}}, IsRestartIdx l₀ → upsilon l₀ < Pv S ηy → ∀ {x y : Ordinal.{0}},
      VbDK S l₀ K x → VbDK S l₀ K y →
      vbTK S l₀ K (Om (1 + 1 + 1) ^ x * y) = Om (1 + 1) ^ vbTK S l₀ K x * vbTK S l₀ K y := fun hl₀ hX₀ _ _ hx hy => by
    have h := faT_Wmul hl₀ hX₀ hKB (k := 1) hx hy
    simpa only [Nat.cast_one] using h
  have hT : vbTK S l K w = Om (1 + 1) ^ vbTK S l K e * vbTK S l K d + vbTK S l K r := by
    conv_lhs => rw [← hdec]
    rw [kzT_add hl hX hKB hWdD hrD, hWmul hl hX heD hdD]
  have hT' : vbTK S l' K w = Om (1 + 1) ^ vbTK S l' K e * vbTK S l' K d + vbTK S l' K r := by
    conv_lhs => rw [← hdec]
    rw [kzT_add hl' hX' hKB hWdD' hrD', hWmul hl' hX' heD' hdD']
  have hTW : ∀ {l₀ : Ordinal.{0}} {ηy : Ordinal.{0}}, IsRestartIdx l₀ → upsilon l₀ < Pv S ηy → VbDK S l₀ K e →
      vbTK S l₀ K (Om (1 + 1 + 1) ^ e) = Om (1 + 1) ^ vbTK S l₀ K e := fun {l₀ _} hl₀ hX₀ he => by
    have h := hWmul hl₀ hX₀ he (faPC_D (S := S) (l := l₀) hKB).one
    rwa [mul_one, fa_T_one hl₀ hX₀ hKB, mul_one] at h
  have hTd2 := fa_T_lt_O2 hl hX hKB hdD hd3
  have hTd0 : vbTK S l K d ≠ 0 := by
    have h := vbTK_mono hl hX hKB hPC.zero hdD (pos_iff_ne_zero.2 hd0)
    rw [vbTK_zero hl hX hKB] at h
    exact h.ne'
  have hTrlt : vbTK S l K r < Om (1 + 1) ^ vbTK S l K e := by
    rw [← hTW hl hX heD]; exact vbTK_mono hl hX hKB hrD hWeD hrlt
  have hTe1 : 1 ≤ vbTK S l K e := by
    have h := (vbTK_le_iff hl hX hKB hPC.one heD).1 he1
    rwa [fa_T_one hl hX hKB] at h
  have hTd2' : vbTK S l K d < OmTwo := by rw [hO2]; exact hTd2
  have hTrlt' : vbTK S l K r < OmTwo ^ vbTK S l K e := by rw [hO2]; exact hTrlt
  have hu : u = OmTwo ^ vbTK S l K e * vbTK S l K d + vbTK S l K r := by rw [← hTw, hT, hO2]
  obtain ⟨hlog, hdiv, hmod⟩ := uc_cnf_parts hTd0 hTd2' hTrlt'
  rw [← hu] at hlog hdiv hmod
  have hcomps := ucComps_big hu2' huE
  rw [hlog] at hcomps
  rw [hlog] at hdiv hmod
  rw [hdiv, hmod] at hcomps
  have heu : vbTK S l K e < u := by
    have := uc_log_lt hu2' huE; rwa [hlog] at this
  have hru : vbTK S l K r < u := by
    have := uc_mod_lt hu2'; rwa [hlog, hmod] at this
  have hE' := IH _ heu (heu.trans huE) e heD heD' rfl (fun v hv => hA v (by rw [hcomps]; exact Or.inl hv))
  have hR' := IH _ hru (hru.trans huE) r hrD hrD' rfl (fun v hv => hA v (by rw [hcomps]; exact Or.inr (Or.inr hv)))
  have hfd := hf d hdD hdD' hTd2 (hA _ (by rw [hcomps]; exact Or.inr (Or.inl rfl)))
  have hdT' := fa_T_lt_O2 hl' hX' hKB hdD' hd3
  refine ⟨?_, ?_⟩
  · rw [hu, ucMap_cnf f hTe1 hTd0 hTd2' hTrlt' (hu ▸ huE), hE'.1, hR'.1, hfd, hT', hO2]
  · rw [hT']
    have hO2E : Om (1 + 1 : Ordinal.{0}) < ucE := by rw [← hO2]; exact ucE_gt
    have h1 : Om (1 + 1) * vbTK S l' K e < ucE := uc_E_mulPrin hO2E hE'.2
    have h2 : Om (1 + 1) ^ vbTK S l' K e < ucE := by
      rw [Ui.ui_W_eq 1]
      have := (isNormal_opow one_lt_omega0).strictMono h1
      rwa [ucE_fix] at this
    exact uc_E_indec (uc_E_mulPrin h2 (hdT'.trans hO2E)) hR'.2

/-- **`vcSub Ψ (T x) = T' x` below `B₂`**, every leaf of `T x` good. -/
theorem faLevLow {Ψ : Ordinal.{0} → Ordinal.{0}} (hAW : Om ω ≤ ConjT.Aη S (cdEta S l))
    (hAW' : Om ω ≤ ConjT.Aη S (cdEta S l')) :
    ∀ z, z < ucB → VcLv (FaGood S l l' Ψ) z → ∀ x, VbDK S l K x → VbDK S l' K x → vbTK S l K x = z →
      vcSub Ψ z = vbTK S l' K x := by
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hO2 : (OmTwo : Ordinal.{0}) = Om (1 + 1) := Uc.uc_Om2_eq
  have hPC := faPC_D (S := S) (l := l) hKB
  have hPC' := faPC_D (S := S) (l := l') hKB
  have hB2 : (ucB : Ordinal.{0}) < Om (1 + 1) := Yv.yv_B_lt_Om2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB hL x hx hx' hTx
  rcases lt_trichotomy z Om1 with hz1 | rfl | hz1
  · -- a leaf
    obtain ⟨c, hc, hΘ, hΨ⟩ := (VcLv_small _ hz1).1 hL
    have hTx1 : vbTK S l K x < Om 1 := by rw [hTx, ← hO1]; exact hz1
    have hx2 := fa_lt_O2 hl hX hKB hx hTx1
    have hxc : GxCl (upsilon l) (ldAtR S l) x := (ldHull_iff hl hX hx2).1 hx.1
    have hTc : gxTh (upsilon l) (ldAtR S l) x = z := by rw [← vbTK_code hl hX hKB hx2 hx.1]; exact hTx
    have hcx : c = x := by
      rcases lt_trichotomy c x with h | h | h
      · exact absurd ((gxTh_lt hc h).trans_eq hTc) (by rw [hΘ]; exact lt_irrefl _)
      · exact h
      · exact absurd ((gxTh_lt hxc h).trans_eq hΘ) (by rw [hTc]; exact lt_irrefl _)
    subst hcx
    rw [vcSub_small Ψ hz1, hΨ, vbTK_code hl' hX' hKB hx2 hx'.1]
  · -- `Ω₁`
    have hx2 : x = Om (1 + 1) := vbTK_inj hl hX hKB hx (fa_O2_D hKB) (by rw [hTx, fa_T_O2 hl hX hKB, hO1])
    rw [vcSub_Om1, hx2, fa_T_O2 hl' hX' hKB, hO1]
  -- `Ω₁ < z`
  have hz1' : Om 1 < z := by rw [← hO1]; exact hz1
  have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
    have := fa_T_lt_O1 hl hX hKB hx hc
    rw [hTx] at this
    exact absurd this (not_lt.2 hz1'.le)
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
    rw [← e, fa_T_O2 hl hX hKB] at hTx
    exact absurd hz1' (by rw [← hTx]; exact lt_irrefl _)
  have hx0 : x ≠ 0 := ((Ui.ui_SC_W 1).1.trans hx2).ne'
  by_cases hE : ω ^ z = z
  · have hxε : ω ^ x = x := (fa_T_eps_iff hl hX hKB hx hx2le).2 (by rw [hTx]; exact hE)
    by_cases hI : invVeblen₁ z < z
    · -- `φ`
      have hb2 : invVeblen₂ z < z := Tf.tf_inv2_lt hE
      have hvz : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      have hzS : ¬ SC z := fun h => by
        have := h.2 _ hI _ hb2
        rw [hvz] at this
        exact lt_irrefl _ this
      have hxS : ¬ SC x := fun h => hzS (hTx ▸ (fa_T_SC_iff hl hX hKB hx hx2).1 h)
      obtain ⟨haD, hbD, -, -, -, -, e1, e2, -⟩ := fa_shape_veb hl hX hKB hx hx2 hxε hxS
      obtain ⟨haD', hbD', -, -, -, -, -, -, hT'⟩ := fa_shape_veb hl' hX' hKB hx' hx2 hxε hxS
      rw [hTx] at e1 e2
      obtain ⟨hL1, hL2⟩ := (VcLv_phi _ hz1 hzB hE hI).1 hL
      rw [vcSub_phi Ψ hz1 hzB hE hI, hT', IH _ hI (hI.trans hzB) hL1 _ haD haD' e1.symm,
        IH _ hb2 (hb2.trans hzB) hL2 _ hbD hbD' e2.symm]
    · -- an atom
      have hzS : SC z := Tl.tl_SC_of hz1 hI
      have hxS : SC x := (fa_T_SC_iff hl hX hKB hx hx2).2 (by rw [hTx]; exact hzS)
      have hzΩ2 : z < Om (1 + 1) := hzB.trans hB2
      have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
        rintro ⟨j, rfl⟩
        have hj : 2 ≤ j := by
          have h := Om_le_Om.1 hx2le
          rw [one_add_one_eq_two] at h
          have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
          exact_mod_cast h'
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
        rw [Nat.cast_succ] at hTx
        rw [e] at hTx
        have hi : (1 : Ordinal.{0}) ≤ i := by
          have : 1 ≤ i := by omega
          exact_mod_cast this
        rcases hi.lt_or_eq with h | h
        · exact absurd ((Om_le_Om.2 (Order.add_one_le_of_lt h)).trans_lt (hTx ▸ hzΩ2)) (lt_irrefl _)
        · rw [← h] at hTx; exact absurd hz1' (by rw [← hTx]; exact lt_irrefl _)
      have hW : x ≠ Om ω := fun e => by
        rw [e, vbTK_OmW hl hX hKB (e ▸ hx.2.2)] at hTx
        exact absurd (hTx ▸ hzΩ2) (not_lt.2 (Om_le_Om.2 (Ui.ui_s1_lt_omega one_lt_omega0).le))
      obtain ⟨k, hk, hk1, hk2, γ, y, hγ, hy, hxe⟩ := fa_shape_atom hl hX hKB hx hx2 hxS hΩ hW
      obtain rfl : k = 1 := by
        by_contra hne
        have hk2' : 2 ≤ k := by omega
        have hk3 : Om (1 + 1 + 1) ≤ x := by
          refine (Om_le_Om.2 ?_).trans hk1.le
          have h' : ((2 : ℕ) : Ordinal.{0}) ≤ k := by exact_mod_cast hk2'
          have e : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
          rw [e] at h'
          exact add_le_add h' le_rfl
        have := vbTK_ge_lev hl hX hKB hx 1 (by simpa using hk3)
        rw [hTx] at this
        exact absurd (by simpa using this) (not_le.2 hzΩ2)
      simp only [Nat.cast_one] at hγ hk1 hk2 hxe
      subst hxe
      have hA1 := faAtom hl hX hKB (k := 1) le_rfl (by simpa using hγ) (by simpa using hy) (by simpa using hk2) (by simpa using hx)
      have hA2 := faAtom hl' hX' hKB (k := 1) le_rfl (by simpa using hγ) (by simpa using hy) (by simpa using hk2) (by simpa using hx')
      simp only [Nat.cast_one] at hA1 hA2
      obtain ⟨hγD, hyD, hμV, hTz⟩ := hA1
      obtain ⟨hγD', hyD', hμV', hTz'⟩ := hA2
      rw [hTz] at hTx
      set μ := vbTK S l K γ with hμdef
      set v := vbTK S l K y with hvdef
      have hvz : v < z := by
        rw [← hTx]
        have := vbTK_mono hl hX hKB hyD hx hy
        rwa [hTz] at this
      have hvz0 : v < ulH S 1 μ v := by rw [hTx]; exact hvz
      -- the normal form of `R2.UcDat`
      obtain ⟨hLev, hIdx⟩ := Vp.vpLev_H (S := S) (s := 1) hμV hvz0
      obtain ⟨hUL, hUI⟩ := Vd.vdLev_eq_uc (S := S) hzS hz1' hzB
      rw [Vp.vpLev_one, hTx] at hLev
      rw [hLev] at hUL
      have hne := uc_nf_of_lt hzS hz1 hzB
      obtain ⟨hlE, -, -, -, -⟩ := ucLev_spec hzS hz1 hne
      have hμE : μ < ucE := by rw [hUL]; exact hlE
      have hzH : ucH μ v = z := by
        have := (Vd.vd_lev_uc (S := S) hμE hzS hz1').1
        rw [← this]; exact hTx
      have hvz1 : v < ucH μ v := by rw [hzH]; exact hvz
      have hparts := (VcLv_atom _ hz1 hzB hE hI).1 hL
      set f' : Ordinal.{0} → Ordinal.{0} := fun u => if u < z then vcSub Ψ u else u with hf'
      have hf'lt : ∀ u, u < z → f' u = vcSub Ψ u := fun u hu => if_pos hu
      have hmain : ∀ u, u ∈ ucParts z → u < z → ∀ w, VbDK S l K w → VbDK S l' K w → vbTK S l K w = u →
          f' u = vbTK S l' K w := fun u hu huz w hw hw' hT => by
        rw [hf'lt u huz]
        exact IH u huz (huz.trans hzB) (hparts u hu huz) w hw hw' hT
      rw [vcSub_atom Ψ hz1 hzB hE hI, hTz']
      change ucRebuild f' z = _
      have hzz : ucRebuild f' z = ucRebuild f' (ucH μ v) := by rw [hzH]
      rw [hzz]
      by_cases hXz : z < tlX
      · -- below `X`
        obtain ⟨hβz, hβne, -⟩ := tlLev_spec hzS hz1 hXz
        have hμβ : μ = tlLev z := by
          rw [hUL]
          have hβO2 : tlLev z < OmTwo := (hβz.trans hXz).trans tlX_lt_OmTwo
          have hi := (tl_nf hzS hz1 hXz).1
          have hmax : max Om1 (tlLev z) < z := max_lt hz1 hβz
          obtain ⟨y', hy'⟩ := (uc_range_F hβO2 hmax).2 ⟨_, hi⟩
          have hy'z : y' < ucH (tlLev z) y' := by
            rw [hy']
            refine lt_of_le_of_ne ?_ fun e => ?_
            · rw [← hy']; exact (ucH_normal _).strictMono.le_apply
            · rw [e] at hy'
              exact hβne ((ucH_fix_iff_F hβO2 hmax).1 hy')
          have := (ucLev_H (hβO2.trans ucE_gt) hy'z).1
          rw [hy'] at this
          exact this
        have hμz : μ < z := by rw [hμβ]; exact hβz
        have hμX : μ < tlX := hμz.trans hXz
        have hμ2 : μ < OmTwo := hμX.trans tlX_lt_OmTwo
        set i := ucS μ + v with hidef
        have hzF : ucH μ v = rhF μ i := ucH_eq_F hμ2 v
        have hmaxμ : max Om1 μ < z := max_lt hz1 hμz
        have hiz : i < z := hzS.isPrincipal (ucS_lt hmaxμ hzS) hvz
        have hFz : rhF μ i = z := hzF.symm.trans hzH
        have hiF : i < rhF μ i := by rw [hFz]; exact hiz
        have hXF : rhF μ i < tlX := by rw [hFz]; exact hXz
        have hpF : ucParts z = {μ, i} := by rw [← hFz]; exact ucParts_F hXF hiF
        have hpμ : μ ∈ ucParts z := by rw [hpF]; exact Or.inl rfl
        have hpi : i ∈ ucParts z := by rw [hpF]; exact Or.inr rfl
        rw [hzF, ucRebuild_F f' hXF hiF, hmain μ hpμ hμz γ hγD hγD' rfl]
        have hTH : ∀ {g : Ordinal.{0}}, g < tlX → ulH S 1 g (vbTK S l' K y) = rhF g (Gl.glY0 g + vbTK S l' K y) := fun {g} hg => by
          have hS' : SC (ulH S 1 g (vbTK S l' K y)) := ulH_SC _ _
          have hO' : Om 1 < ulH S 1 g (vbTK S l' K y) := ulH_gt _ _
          have hgE : g < ucE := (hg.trans tlX_lt_OmTwo).trans ucE_gt
          rw [(Vd.vd_lev_uc (S := S) hgE hS' hO').1, ucH_eq_F (hg.trans tlX_lt_OmTwo), Qc.qc_ucS_low hg]
        have hO1X : (Om1 : Ordinal.{0}) < tlX := tlX_gt
        rcases lt_trichotomy μ Om1 with hμ1 | hμ1 | hμ1
        · -- `μ < Ω₁`
          have hγ2 : γ < Om (1 + 1) := fa_lt_O2 hl hX hKB hγD (by rw [← hO1]; exact hμ1)
          have hT'γ : vbTK S l' K γ < Om1 := by rw [hO1]; exact fa_T_lt_O1 hl' hX' hKB hγD' hγ2
          have h1D := hPC.one
          have h1D' := hPC'.one
          have hx₁ : VbDK S l K (Om (1 + 1) + 1 + y) := hPC.add (hPC.add (fa_O2_D hKB) h1D) hyD
          have hx₁' : VbDK S l' K (Om (1 + 1) + 1 + y) := hPC'.add (hPC'.add (fa_O2_D hKB) h1D') hyD'
          have hTx₁ : vbTK S l K (Om (1 + 1) + 1 + y) = i := by
            rw [kzT_add hl hX hKB (hPC.add (fa_O2_D hKB) h1D) hyD, kzT_add hl hX hKB (fa_O2_D hKB) h1D,
              fa_T_O2 hl hX hKB, fa_T_one hl hX hKB, hidef, Qc.qc_ucS_low hμX, Gl.glY0_lt hμ1, hO1]
          have hTx₁' : vbTK S l' K (Om (1 + 1) + 1 + y) = Om1 + 1 + vbTK S l' K y := by
            rw [kzT_add hl' hX' hKB (hPC'.add (fa_O2_D hKB) h1D') hyD', kzT_add hl' hX' hKB (fa_O2_D hKB) h1D',
              fa_T_O2 hl' hX' hKB, fa_T_one hl' hX' hKB, hO1]
          rw [hmain i hpi hiz _ hx₁ hx₁' hTx₁, hTx₁', hTH (hT'γ.trans hO1X), Gl.glY0_lt hT'γ]
        · -- `μ = Ω₁`
          have hγ2 : γ = Om (1 + 1) := vbTK_inj hl hX hKB hγD (fa_O2_D hKB) (by
            rw [fa_T_O2 hl hX hKB, ← hO1]; exact hμ1)
          have hT'γ : vbTK S l' K γ = Om1 := by rw [hγ2, fa_T_O2 hl' hX' hKB, hO1]
          have hx₁ : VbDK S l K (1 + y) := hPC.add hPC.one hyD
          have hx₁' : VbDK S l' K (1 + y) := hPC'.add hPC'.one hyD'
          have hTx₁ : vbTK S l K (1 + y) = i := by
            rw [kzT_add hl hX hKB hPC.one hyD, fa_T_one hl hX hKB, hidef, Qc.qc_ucS_low hμX, hμ1, Gl.glY0_eq]
          have hTx₁' : vbTK S l' K (1 + y) = 1 + vbTK S l' K y := by
            rw [kzT_add hl' hX' hKB hPC'.one hyD', fa_T_one hl' hX' hKB]
          rw [hmain i hpi hiz _ hx₁ hx₁' hTx₁, hTx₁', hTH (by rw [hT'γ]; exact hO1X), hT'γ, Gl.glY0_eq]
        · -- `Ω₁ < μ < X`
          have hO1μ : Om 1 < vbTK S l K γ := by rw [← hO1]; exact hμ1
          have hγ2 : Om (1 + 1) < γ := by
            have h : vbTK S l K (Om (1 + 1)) < vbTK S l K γ := by rw [fa_T_O2 hl hX hKB]; exact hO1μ
            by_contra hc
            exact absurd h (not_lt.2 ((vbTK_le_iff hl hX hKB hγD (fa_O2_D hKB)).1 (not_lt.1 hc)))
          have hT'O : Om1 < vbTK S l' K γ := by
            have h := vbTK_mono hl' hX' hKB (fa_O2_D hKB) hγD' hγ2
            rwa [fa_T_O2 hl' hX' hKB, ← hO1] at h
          obtain ⟨hXD, hXT⟩ := fa_X hl hX hKB hAW
          obtain ⟨hXD', hXT'⟩ := fa_X hl' hX' hKB hAW'
          have hγX : γ < S.psi (Om (1 + 1 + 1) ^ Om (1 + 1 + 1 : Ordinal.{0})) (Om (1 + 1 + 1)) := by
            by_contra hc
            have h := (vbTK_le_iff hl hX hKB hXD hγD).1 (not_lt.1 hc)
            rw [hXT] at h
            exact absurd hμX (not_lt.2 h)
          have hT'X : vbTK S l' K γ < tlX := by
            have h := vbTK_mono hl' hX' hKB hγD' hXD' hγX
            rwa [hXT'] at h
          have hiv : i = v := by rw [hidef, Qc.qc_ucS_low hμX, Gl.glY0_gt hμ1, zero_add]
          rw [hiv, hmain v (by rw [← hiv]; exact hpi) hvz y hyD hyD' rfl, hTH hT'X, Gl.glY0_gt hT'O, zero_add]
      · -- from `X` on
        have hX1 : tlX ≤ ucH μ v := by rw [hzH]; exact not_lt.1 hXz
        have hpartsH : ∀ u, u ∈ ucComps μ ∪ {v} → u ∈ ucParts z := fun u hu => by
          rw [← hzH, ucParts_H hμE hvz1 hX1]; exact hu
        have hcompLt : ∀ u, u ∈ ucComps μ → u < z := fun u hu => by
          have hC : ucC μ < z := by
            have := ucH_C_lt μ v; rwa [hzH] at this
          exact ((ucC_lt_iff hzS.1 μ).1 hC) u hu
        have hA : ∀ w, VbDK S l K w → VbDK S l' K w → vbTK S l K w < Om (1 + 1) →
            vbTK S l K w ∈ {u | u ∈ ucComps μ} → f' (vbTK S l K w) = vbTK S l' K w := fun w hw hw' _ hmem =>
          hmain _ (hpartsH _ (Or.inl hmem)) (hcompLt _ hmem) w hw hw' rfl
        obtain ⟨hM, hE'⟩ := fa_ucMap hl hX hl' hX' hKB hA μ hμE γ hγD hγD' rfl fun u hu => hu
        rw [ucRebuild_H f' hμE hvz1 hX1, hM, hmain v (hpartsH v (Or.inr rfl)) hvz y hyD hyD' rfl]
        have hS' : SC (ulH S 1 (vbTK S l' K γ) (vbTK S l' K y)) := ulH_SC _ _
        have hO' : Om 1 < ulH S 1 (vbTK S l' K γ) (vbTK S l' K y) := ulH_gt _ _
        rw [(Vd.vd_lev_uc (S := S) hE' hS' hO').1]
  · -- the Cantor normal form
    have hxε : ω ^ x ≠ x := fun h => hE (by rw [← hTx]; exact (fa_T_eps_iff hl hX hKB hx hx2le).1 h)
    obtain ⟨n, -, hdec, hlD, hrD, -, -, hTr, hlog, hmod, hdiv⟩ := fa_shape_cnf hl hX hKB hx hx0
    obtain ⟨n', -, hdec', hlD', hrD', -, hT', -, -, -, -⟩ := fa_shape_cnf hl' hX' hKB hx' hx0
    have hpos : ω ^ log ω x ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hrl : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos
    have hnn : (n : Ordinal.{0}) = n' := by
      have key : ∀ m : ℕ, x = ω ^ log ω x * m + x % ω ^ log ω x → x / ω ^ log ω x = m := fun m hm => by
        have h := congrArg (· / ω ^ log ω x) hm
        simp only at h
        rw [h, Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hrl, add_zero]
      rw [← key n hdec, key n' hdec']
    have hx1' : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
    have hlx : log ω x < x := ruLog_lt hx1' hxε
    have hrx : x % ω ^ log ω x < x := mod_opow_log_lt_self ω hx0
    have hl2 : Om (1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [gg_SC_eps ldOm2_SC]; exact hx2le)
    subst hTx
    obtain ⟨hL1, hL2⟩ := (VcLv_cnf _ hz1 hzB hE).1 hL
    rw [hlog] at hL1 hL2
    rw [hmod] at hL2
    have hTlz : vbTK S l K (log ω x) < vbTK S l K x := vbTK_mono hl hX hKB hlD hx hlx
    have hTrz : vbTK S l K (x % ω ^ log ω x) < vbTK S l K x := vbTK_mono hl hX hKB hrD hx hrx
    have hR := IH _ hTrz (hTrz.trans hzB) hL2 _ hrD hrD' rfl
    rw [vcSub_cnf Ψ hz1 hzB hE, hlog, hmod, hdiv, hR, hT', ← hnn]
    congr 2
    by_cases hε : ω ^ vbTK S l K (log ω x) = vbTK S l K (log ω x)
    · rw [if_pos hε] at hL1 ⊢
      have hLε : ω ^ log ω x = log ω x := (fa_T_eps_iff hl hX hKB hlD hl2).2 hε
      have hLε' := (fa_T_eps_iff hl' hX' hKB hlD' hl2).1 hLε
      rw [IH _ hTlz (hTlz.trans hzB) hL1 _ hlD hlD' rfl, hLε']
    · rw [if_neg hε] at hL1 ⊢
      set b := log ω x - Om (1 + 1) with hbdef
      have hbD : VbDK S l K b := hPC.sub hlD (fa_O2_D hKB) hl2
      have hbD' : VbDK S l' K b := hPC'.sub hlD' (fa_O2_D hKB) hl2
      have he : Om (1 + 1) + b = log ω x := Ordinal.add_sub_cancel_of_le hl2
      have hTℓ : vbTK S l K (log ω x) = Om1 + vbTK S l K b := by
        rw [← he, kzT_add hl hX hKB (fa_O2_D hKB) hbD, fa_T_O2 hl hX hKB, hO1]
      have hTℓ' : vbTK S l' K (log ω x) = Om1 + vbTK S l' K b := by
        rw [← he, kzT_add hl' hX' hKB (fa_O2_D hKB) hbD', fa_T_O2 hl' hX' hKB, hO1]
      have hsub : vbTK S l K (log ω x) - Om1 = vbTK S l K b := by
        rw [hTℓ, Ordinal.add_sub_cancel]
      rw [hsub] at hL1 ⊢
      have hbl : b ≤ log ω x := Ordinal.sub_le_self _ _
      have hTbz : vbTK S l K b < vbTK S l K x := vbTK_mono hl hX hKB hbD hx (hbl.trans_lt hlx)
      rw [IH _ hTbz (hTbz.trans hzB) hL1 _ hbD hbD' rfl, hTℓ', opow_add, Rj.rj_Om1_opow]

/-- **`YvR Ψ (T x) (T' x)`**: every leaf of `T x` good. -/
theorem faLevR {Ψ : Ordinal.{0} → Ordinal.{0}} (hAW : Om ω ≤ ConjT.Aη S (cdEta S l))
    (hAW' : Om ω ≤ ConjT.Aη S (cdEta S l')) :
    ∀ z, YvLv S (FaGood S l l' Ψ) z → ∀ x, VbDK S l K x → VbDK S l' K x → vbTK S l K x = z →
      YvR S Ψ z (vbTK S l' K x) := by
  intro z hz
  induction hz with
  | low hB hL =>
    intro x hx hx' hT
    have h := faLevLow hl hX hl' hX' hKB hAW hAW' _ hB hL x hx hx' hT
    rw [← h]; exact YvR.low hB
  | @om s z h1s hs hzs =>
    intro x hx hx' hT
    obtain ⟨n, rfl⟩ := lt_omega0.1 hs
    have hn1 : 1 ≤ n := by
      have : (1 : Ordinal.{0}) < n := h1s
      have h' : 1 < n := by exact_mod_cast this
      omega
    have hxe : x = Om ((n : Ordinal.{0}) + 1) := by
      refine vbTK_inj hl hX hKB hx (fa_Om1_D hKB n) ?_
      rw [hT, hzs, vbTK_Om hl hX hKB hn1]
    have hz' : vbTK S l' K x = z := by rw [hxe, vbTK_Om hl' hX' hKB hn1, hzs]
    rw [hz']
    exact YvR.om h1s hs hzs
  | @cnf s z h1s hs hz1 hz2 hzB hE _ _ ihl ihr =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx0 : x ≠ 0 := ((Ui.ui_SC_W 1).1.trans_le hx2le).ne'
    have hxε : ω ^ x ≠ x := fun h => hE (by rw [← hT]; exact (fa_T_eps_iff hl hX hKB hx hx2le).1 h)
    obtain ⟨n, -, hdec, hlD, hrD, -, -, -, hlog, hmod, hdiv⟩ := fa_shape_cnf hl hX hKB hx hx0
    obtain ⟨n', -, hdec', hlD', hrD', -, hT', -, -, -, -⟩ := fa_shape_cnf hl' hX' hKB hx' hx0
    have hpos : ω ^ log ω x ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hrl : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos
    have hnn : (n : Ordinal.{0}) = n' := by
      have key : ∀ m : ℕ, x = ω ^ log ω x * m + x % ω ^ log ω x → x / ω ^ log ω x = m := fun m hm => by
        have h := congrArg (· / ω ^ log ω x) hm
        simp only at h
        rw [h, Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hrl, add_zero]
      rw [← key n hdec, key n' hdec']
    have hl2 : Om (1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [gg_SC_eps ldOm2_SC]; exact hx2le)
    subst hT
    have hR1 := ihl _ hlD hlD' hlog.symm
    have hR2 := ihr _ hrD hrD' (by rw [hlog, hmod])
    have h := YvR.cnf h1s hs hz1 hz2 hzB hE hR1 hR2
    rw [hlog, hdiv] at h
    rw [hT', ← hnn]
    by_cases hε : ω ^ vbTK S l K (log ω x) = vbTK S l K (log ω x)
    · rw [if_pos hε] at h
      have hLε : ω ^ log ω x = log ω x := (fa_T_eps_iff hl hX hKB hlD hl2).2 hε
      rw [(fa_T_eps_iff hl' hX' hKB hlD' hl2).1 hLε]
      exact h
    · rw [if_neg hε] at h
      exact h
  | @veb s z h1s hs hz1 hz2 hzB hE hS _ _ iha ihb =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
      rw [← e, fa_T_O2 hl hX hKB] at hT
      exact absurd hO1z (by rw [← hT]; exact lt_irrefl _)
    have hxε : ω ^ x = x := (fa_T_eps_iff hl hX hKB hx hx2le).2 (by rw [hT]; exact hE)
    have hxS : ¬ SC x := fun h => hS (hT ▸ (fa_T_SC_iff hl hX hKB hx hx2).1 h)
    obtain ⟨haD, hbD, -, -, -, -, e1, e2, -⟩ := fa_shape_veb hl hX hKB hx hx2 hxε hxS
    obtain ⟨haD', hbD', -, -, -, -, -, -, hT'⟩ := fa_shape_veb hl' hX' hKB hx' hx2 hxε hxS
    rw [hT] at e1 e2
    rw [hT']
    exact YvR.veb h1s hs hz1 hz2 hzB hE hS (iha _ haD haD' e1.symm) (ihb _ hbD hbD' e2.symm)
  | @atom s z h1s hs hz1 hz2 hzB hS _ _ ihγ ihy =>
    intro x hx hx' hT
    have hO1z : Om 1 < z := (Om_le_Om.2 h1s).trans_lt hz1
    have hx2le : Om (1 + 1) ≤ x := not_lt.1 fun hc => by
      have := fa_T_lt_O1 hl hX hKB hx hc
      rw [hT] at this
      exact absurd this (not_lt.2 hO1z.le)
    have hx2 : Om (1 + 1) < x := lt_of_le_of_ne hx2le fun e => by
      rw [← e, fa_T_O2 hl hX hKB] at hT
      exact absurd hO1z (by rw [← hT]; exact lt_irrefl _)
    have hxS : SC x := (fa_T_SC_iff hl hX hKB hx hx2).2 (by rw [hT]; exact hS)
    have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
      rintro ⟨j, rfl⟩
      have hj : 2 ≤ j := by
        have h := Om_le_Om.1 hx2le
        rw [one_add_one_eq_two] at h
        have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
        exact_mod_cast h'
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e := vbTK_Om (S := S) hl hX hKB (k := i) (by omega)
      rw [Nat.cast_succ, e] at hT
      rw [← hT] at hz1 hz2
      exact Yv.yv_Om_not_in hz1 hz2
    have hW : x ≠ Om ω := fun e => by
      rw [e, vbTK_OmW hl hX hKB (e ▸ hx.2.2)] at hT
      rw [← hT] at hz1 hz2
      exact Yv.yv_Om_not_in hz1 hz2
    obtain ⟨k, hk, hk1, hk2, γ, y, hγ, hy, hxe⟩ := fa_shape_atom hl hX hKB hx hx2 hxS hΩ hW
    subst hxe
    obtain ⟨hγD, hyD, hμV, hTz⟩ := faAtom hl hX hKB hk hγ hy hk2 hx
    obtain ⟨hγD', hyD', -, hTz'⟩ := faAtom hl' hX' hKB hk hγ hy hk2 hx'
    rw [hTz'] 
    have hTz1 : Om (k : Ordinal.{0}) < ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) := ulH_gt _ _
    have hTz2 : ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) < Om ((k : Ordinal.{0}) + 1) := by
      rw [← hTz]; exact vbTK_lt_lev hl hX hKB hx k hk2
    rw [hTz] at hT
    have hsk : (k : Ordinal.{0}) = s := by
      rw [← hT] at hz1 hz2
      exact Yv.yv_lev_unique hTz1 hTz2 hz1 hz2
    subst hsk
    have hTy : vbTK S l K y < ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) := by
      rw [← hTz]; exact vbTK_mono hl hX hKB hyD hx hy
    obtain ⟨hLev, hIdx⟩ := Vp.vpLev_H (S := S) (s := (k : Ordinal.{0})) hμV hTy
    rw [hT] at hLev hIdx
    have hR1 := ihγ γ hγD hγD' hLev.symm
    have hR2 : YvR S Ψ (Vp.vpI S k (Vp.vpLev S k z) z) (vbTK S l' K y) := ihy y hyD hyD' (by rw [hLev, hIdx])
    exact YvR.atom h1s hs hz1 hz2 hzB hS hR1 hR2

/-- **`yvSub Ψ (T x) = T' x`.** -/
theorem faLevSub {Ψ : Ordinal.{0} → Ordinal.{0}} (hAW : Om ω ≤ ConjT.Aη S (cdEta S l))
    (hAW' : Om ω ≤ ConjT.Aη S (cdEta S l')) {x : Ordinal.{0}} (hx : VbDK S l K x) (hx' : VbDK S l' K x)
    (hL : YvLv S (FaGood S l l' Ψ) (vbTK S l K x)) : yvSub S Ψ (vbTK S l K x) = vbTK S l' K x :=
  yvSub_eq (faLevR hl hX hl' hX' hKB hAW hAW' _ hL x hx hx' rfl)

end Two

end Googology.Trans.PoR.InaccPsi.R2.Fa
