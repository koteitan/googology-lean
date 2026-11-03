import Googology.Trans.PoR.InaccPsi.R2.YtG2

/-!
# Every base `a + Ω₂·γ` is a base with a law at both ends; every atom in `[ψ₂(a), G^a)` moves

`B_n = Bc.bcB S n`, "window" as in `Yj.yjBlkMove` (`CdRange λ`, `c_n < ρ_λ`, `r(λ) < c_{n+1}`, `λ'` a restart,
`B_n ρ_λ = ρ_{λ'}`, `A'` own with `ψ₁(A') = ρ_{λ'}`), `G^a = ψ₂(a + Ω₂·Ω₂)` (`Yt.ytG`), "IH(s)" = every code
`x < s` of `λ` moves (`MvD x`, `B_n x` code of `λ'`, `B_n x < θ⁺`, `Θx < c_{n+1}`, `Θ'(B_n x) = B_n Θx`).

* `ytOm2sq_D` (`B_n(Ω₂·Ω₂) = Ω₂·Ω₂`), `ytB_G` (`B_n G^a = G^{B_n a}`), `ytDvdWe` (`Ω₂² ∣ W^y` for `y ≥ 2`);
* `ytBaseG` (**`a + Ω₂·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `γ < G^a`, image `D + Ω₁·Θγ`, and
  `B_n(a + Ω₂·γ) = B_n a + Ω₂·B_n γ`, given `Yj.YjBase λ λ' A' a D`, `Ω₂² ∣ a`, `Ω₂² ∣ B_n a` and IH below
  `ψ₂(a + Ω₂·γ)`);
* `ytAtMove` (**EVERY ATOM `ψ₂(a) ≤ s < G^a` MOVES** under IH(s));
* `ytTopMoveG` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Ω₂²)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES**, under the
  premise of WallBelow at `s`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- `B_n(Ω₂·Ω₂) = Ω₂·Ω₂`. -/
theorem ytOm2sq_D {n : ℕ} : MvD S (Om (1 + 1) * Om (1 + 1)) ∧
    Bc.bcB S n (Om (1 + 1) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  have hne : ω ^ (Om (1 + 1 : Ordinal.{0}) + Om (1 + 1)) ≠ Om (1 + 1) + Om (1 + 1) := by
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om (1 + 1) * ω := by
      have e2 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) = Om (1 + 1) * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
      rw [e2]; exact (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (by exact_mod_cast natCast_lt_omega0 2)
    have h2 : Om (1 + 1 : Ordinal.{0}) * ω ≤ ω ^ (Om (1 + 1) + Om (1 + 1)) := by
      rw [ldW2_eq]; exact opow_le_opow_right omega0_pos (add_le_add_right (Order.one_le_iff_ne_zero.2
        ldOm2_SC.1.ne') _)
    rw [h] at h2
    exact absurd h1 (not_lt.2 h2)
  obtain ⟨hDo, hBo⟩ := mvB_opow (k := n) hDs hne
  rw [hBs, hB2, ← ldOm2sq_eq] at hBo
  rw [← ldOm2sq_eq] at hDo
  exact ⟨hDo, hBo⟩

/-- `Ω₂² ∣ W^y` for `y ≥ 2`. -/
theorem ytDvdWe {y : Ordinal.{0}} (hy : 1 + 1 ≤ y) : Om (1 + 1) * Om (1 + 1) ∣ leWe y := by
  unfold leWe
  rw [ldOm2sq_eq]
  refine opow_dvd_opow ω ?_
  calc Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) = Om (1 + 1) * (1 + 1) := by rw [mul_add, mul_one]
    _ ≤ Om (1 + 1) * y := mul_le_mul_right hy _

theorem ytTwo_le_X (k : ℕ) (e : Ordinal.{0}) : (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e := by
  have h2 : (1 + 1 : Ordinal.{0}) < Om 1 := Ph.ph_SC_Om1.isPrincipal one_lt_Om1 one_lt_Om1
  have h3 : Om (1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1) :=
    (Om_lt_Om.2 ((lt_add_one (1 : Ordinal.{0})).trans_le
      (add_le_add_left (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1) 1))).le
  exact (h2.le.trans h3).trans le_self_add

/-- `B_n G^a = G^{B_n a}`. -/
theorem ytB_G {n : ℕ} {a : Ordinal.{0}} (hDa : MvD S a)
    (hown : ∀ d, d ≤ Om (1 + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))) :
    MvD S (ytG S a) ∧ Bc.bcB S n (ytG S a) = ytG S (Bc.bcB S n a) := by
  obtain ⟨hD2, hB2⟩ := ytOm2sq_D (S := S) (n := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDa hD2
  have hmem : a + Om (1 + 1) * Om (1 + 1) ∈ S.CSet (a + Om (1 + 1) * Om (1 + 1))
      (S.psi (a + Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))) :=
    CSet.add_mem (ytOwnAll hown _) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _))
  obtain ⟨hDG, hBG⟩ := mxB_atom (n := n) hDs hmem
  refine ⟨hDG, ?_⟩
  unfold ytG; rw [hBG, hBs, hB2]

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

omit hA' hρ' in
/-- **`a + Ω₂·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `γ < G^a`. -/
theorem ytBaseG {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a)
    (hdvd' : Om (1 + 1) * Om (1 + 1) ∣ Bc.bcB S n a) {γ : Ordinal.{0}}
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγG : γ < ytG S a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (a + Om (1 + 1) * γ) (D + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) ∧
      Bc.bcB S n (a + Om (1 + 1) * γ) = Bc.bcB S n a + Om (1 + 1) * Bc.bcB S n γ := by
  obtain ⟨hX, -, -, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hρSC : SC (upsilon l) := (cdEta_pv (S := S) hl.1 hX) ▸ SC_psi Low.InR_Om_one _
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set A := ConjT.Aη S (cdEta S l) with hAdef
  have haA : a + Om (1 + 1) * Om (1 + 1) < A :=
    (vkOmW.1.isPrincipal hb.D_a.2.2 ldOm2sq_lt_OmW).trans_le (ConjT.OmW_le_A S _)
  have haA' : Bc.bcB S n a + Om (1 + 1) * Om (1 + 1) < ConjT.Aη S (cdEta S l') :=
    (vkOmW.1.isPrincipal hb.D_a'.2.2 ldOm2sq_lt_OmW).trans_le (ConjT.OmW_le_A S _)
  have hγ2 : γ < Om (1 + 1) := hγG.trans (ytG_lt_Om2 a)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  have hγs : γ < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) := ytG_gt hb.own hdvd hγG
  obtain ⟨hDγ, hBγc, -, hΘγX, hΘγ⟩ := IH γ hγ hγs
  -- `B_n(Ω₂·γ) = Ω₂·B_n γ`
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDβ, hBβ⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2
    (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) ∧ x < Om (1 + 1))
    (fun x hx => (IH x hx.1 hx.2.1).1)
    (fun x hx hx0 => by
      obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
      have hlx : log ω x ≤ x := log_le_self ω x
      have hle : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
        ⟨hsub _ (GxCl.opow hρSC.1 hlog) hle, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
          (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩)
    (fun x hx => hx.2.2) γ ⟨hγ, hγs, hγ2⟩
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hb.mv_a hDβ
  rw [hBβ] at hBa
  -- the reading at `λ`
  have hlaw := ytLaw hl hX hb.own hdvd hb.D_a.1 haA hb.hat hb.law γ hγ hγG
  set Θγ := gxTh (upsilon l) (ldAtR S l) γ with hΘγdef
  have hΘγs : Θγ < S.psi (A + D + Om 1 * Θγ) (Om 1) := by rw [← hlaw]; exact gxTh_lt hγ hγs
  have hΘγ1 : Θγ < Om 1 := hΘγs.trans (psi_lt Low.InR_Om_one _)
  have hat := ytHat_own hb.hat hΘγs
  -- `B_n(D + Ω₁·Θγ)`
  obtain ⟨hDΩ, hBΩ⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDΩγ, hBΩγ⟩ := ldB_mulK (n := n) Ph.ph_SC_Om1 hDΩ hBΩ
    (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1)) (fun x hx => mvD_of_lt (hx.2.trans hLw))
    (fun x hx _ => ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩)
    (fun x hx => hx.1) Θγ ⟨hΘγ1, hΘγX⟩
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hb.mv_D hDΩγ
  rw [hBΩγ, ← hΘγ] at hBD
  -- `B_n γ < G^{B_n a}`
  obtain ⟨hDG, hBG⟩ := ytB_G (n := n) hb.mv_a hb.own
  have hBγG : Bc.bcB S n γ < ytG S (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDγ hDG).2 hγG
    rwa [hBG] at h
  have hBγ2 : Bc.bcB S n γ < Om (1 + 1) := hBγG.trans (ytG_lt_Om2 _)
  have hBγH : Bc.bcB S n γ ∈ cdHull S l' := (ldHull_iff hl' hX' hBγ2).2 hBγc
  -- the reading at `λ'`
  have hlaw' := ytLaw hl' hX' hb.own' hdvd' hb.D_a'.1 haA' hb.hat' hb.law' _ hBγc hBγG
  have hΘγs' : gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n γ) <
      S.psi (A' + Bc.bcB S n D + Om 1 * gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n γ)) (Om 1) := by
    rw [← hlaw']
    exact gxTh_lt hBγc (ytG_gt hb.own' hdvd' hBγG)
  have hat' := ytHat_own hb.hat' hΘγs'
  -- the bound `θ`
  have hthG : ∀ {x : Ordinal.{0}}, VbD S l x → ytG S x < ConjT.th S := fun {x} hx =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (vkOmW.1.isPrincipal hx.2.2 ldOm2sq_lt_OmW)
      (CSet.add_mem hx.2.1 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _)))
  have hthG' : ytG S (Bc.bcB S n a) < ConjT.th S :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (vkOmW.1.isPrincipal hb.D_a'.2.2 ldOm2sq_lt_OmW)
      (CSet.add_mem hb.D_a'.2.1 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _)))
  have hΩγW : ∀ {x : Ordinal.{0}}, x < Om (1 + 1) → Om (1 + 1) * x < Om ω := fun hx =>
    (ldOm2_mul_lt hx).trans ldOm2sq_lt_OmW
  refine ⟨⟨⟨CSet.add_mem hb.D_a.1 (ldG2_H hγH),
      CSet.add_mem hb.D_a.2.1 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (hγG.trans (hthG hb.D_a)))),
      vkOmW.1.isPrincipal hb.D_a.2.2 (hΩγW hγ2)⟩,
    ytDvdG hdvd γ, ytBase_own hb.own hdvd hγG, hDa, hDD, by rw [← add_assoc]; exact hat,
    by rw [← add_assoc]; exact hlaw, ?_, ?_, ?_, ?_, ?_⟩, hBa⟩
  · rw [hBa]
    exact ⟨CSet.add_mem hb.D_a'.1 (ldG2_H hBγH),
      CSet.add_mem hb.D_a'.2.1 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (hBγG.trans hthG'))),
      vkOmW.1.isPrincipal hb.D_a'.2.2 (hΩγW hBγ2)⟩
  · rw [hBa]; exact ytDvdG hdvd' _
  · rw [hBa]; exact ytBase_own hb.own' hdvd' hBγG
  · rw [hBD, ← add_assoc]; exact hat'
  · rw [hBa, hBD, ← add_assoc]; exact hlaw'

/-- **EVERY ATOM `ψ₂(a) ≤ s < G^a` MOVES** above a base with a law at both ends with `Ω₂² ∣ a`, `Ω₂² ∣ B_n a`. -/
theorem ytAtMove {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hdvd : Om (1 + 1) * Om (1 + 1) ∣ a)
    (hdvd' : Om (1 + 1) * Om (1 + 1) ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsG : s < ytG S a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  rcases ytClsAll hl hX hb.own hdvd hs hsG with hle | ⟨γ, hγ, hγG, c, hc, hcF, rfl⟩
  · have e : s = S.psi (a + 0) (Om (1 + 1)) := by rw [add_zero]; exact le_antisymm hle hsa
    subst e
    obtain ⟨hD, -, hat, hmv⟩ := yjBlkMove hR h1 hr hl' hB hA' hρ' hb (GxCl.zero (mvUps_pos hl))
      ((Om_pos one_ne_zero).trans (ldOm1_lt_Top _)) IH
    exact ⟨hD, hat, hmv⟩
  · have hle : S.psi (a + Om (1 + 1) * γ) (Om (1 + 1)) ≤ S.psi (a + Om (1 + 1) * γ + c) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1
    obtain ⟨hbγ, -⟩ := ytBaseG hR h1 hr hl' hB hb hdvd hdvd' hγ hγG
      fun x hx hxs => IH x hx (hxs.trans_le hle)
    obtain ⟨hD, -, hat, hmv⟩ := yjBlkMove hR h1 hr hl' hB hA' hρ' hbγ hc hcF IH
    exact ⟨hD, hat, hmv⟩

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Ω₂²)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the premise of
WallBelow at `s`. -/
theorem ytTopMoveG (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsG : s < ytG S (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hd : Om (1 + 1) * Om (1 + 1) ∣ β + leWe (X + e) :=
    dvd_add ((ytDvdWe (ytTwo_le_X k e)).trans hbe.1) (ytDvdWe (ytTwo_le_X k e))
  have hd' : Om (1 + 1) * Om (1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]
    exact dvd_add ((ytDvdWe (ytTwo_le_X k _)).trans hdv') (ytDvdWe (ytTwo_le_X k _))
  exact ytAtMove hR h1 hr hl' hB hA' hρ' hbt hd hd' hs hst hsG IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yt
