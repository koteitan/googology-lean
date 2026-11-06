import Googology.Trans.PoR.InaccPsi.R2.KuJump

/-!
# Ku: THE TOP LAW AT EVERY SUCCESSOR EXPONENT, from the law below (any exponent `E'` of `D`)

`Θ`, `T`, `D`, `A`, `W^x = leWe x`, `Ω^x = leOe x` as before.  `KuN b`: `b ∈ D` is normal, `Ω₃ ∣ b`, `Ω₃ ≤ b` (the
domain of `Zp.ZpTopLawAll`); `KuLaw b`: the top law at `b`.

At `b = β + W^{E'+1}·(γ' + 1)` (`W^{E'+2} ∣ β`, `γ' + 1 < θ` a code, `Ω₃ ≤ E'`) the context is `G(v) = β' + W^{E'}·v`,
`β' = β + W^{E'+1}·γ'`, `G(Ω₂) = b`; its image `T(G v) = T β' + Ω^{T E'}·Θ v` has the gap toward `T b` at `HCl`
(`Kt.ktG_KaT`); the constants `E'`, `γ'` of `G` lie in `Cl(b, ψ₂ b)`, hence (the stages of the plateau, `Kg.kgKey`)
in `Cl(G(x_N), ψ₂(G(x_N)))` for an iterate `x_N`, so `G(v)` is normal for every code `v ≥ x_N` below `ψ₂ b` (the
coefficient `v` is owned, `Kt.ktOwnTw`).  `Ku.kuJump` then gives the law at `b` from the law at the `G(v)`.

* `KuN`, `KuLaw`, `kuSuccE` (**THE TOP LAW AT EVERY SUCCESSOR EXPONENT FROM THE LAW BELOW**: no hypothesis on `E'`).

No new axiom.  New definitions: `KuN`, `KuLaw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ku

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Kg Googology.Trans.PoR.InaccPsi.R2.Kh Googology.Trans.PoR.InaccPsi.R2.Kj
  Googology.Trans.PoR.InaccPsi.R2.Kt Googology.Trans.PoR.InaccPsi.R2.Ks

variable {S : InaccSeq.{0}}

/-- **The domain of the top law**: `b ∈ D` normal, `Ω₃ ∣ b`, `Ω₃ ≤ b`. -/
def KuN (S : InaccSeq.{0}) (l b : Ordinal.{0}) : Prop :=
  VbD S l b ∧ b ∈ S.CSet b (S.psi b (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ b ∧ Om (1 + 1 + 1) ≤ b

/-- **The top law at `b`.** -/
def KuLaw (S : InaccSeq.{0}) (l A b : Ordinal.{0}) : Prop :=
  gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) = S.psi (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) (Om 1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE TOP LAW AT EVERY SUCCESSOR EXPONENT FROM THE LAW BELOW.** -/
theorem kuSuccE {β E' γ' : Ordinal.{0}} (hdv : leWe (E' + 1 + 1) ∣ β) (hγc : GxCl (upsilon l) (ldAtR S l) γ')
    (hγθ : γ' + 1 < ConjT.th S) (hE3 : Om (1 + 1 + 1) ≤ E') (hb : KuN S l (β + leWe (E' + 1) * (γ' + 1)))
    (IH : ∀ a, KuN S l a → a < β + leWe (E' + 1) * (γ' + 1) → KuLaw S l A a) :
    KuLaw S l A (β + leWe (E' + 1) * (γ' + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hZρ, hZρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hZρ.1
  set E := E' + 1 with hEdef
  set b := β + leWe E * (γ' + 1) with hbdef
  set β' := β + leWe E * γ' with hβ'def
  obtain ⟨hbD, hbn, -, -⟩ := hb
  have hγ2 : γ' + 1 < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hγ'2 : γ' < Om (1 + 1) := (lt_add_one γ').trans hγ2
  have hγ0 : γ' + 1 ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_one γ')).ne'
  have hγ'H : γ' ∈ cdHull S l := (ldHull_iff hl hX hγ'2).2 hγc
  -- the components of `b`
  have hEγ := kjEfrom hdv hγ0 hγ2 hbn
  have hE'm : E' ∈ S.CSet b (S.psi b (Om (1 + 1))) := mem_of_add_one_mem hEγ.1
  have hγ'm : γ' ∈ S.CSet b (S.psi b (Om (1 + 1))) := mem_of_add_one_mem hEγ.2
  have hlt1 : leWe E * (γ' + 1) < leWe (E + 1) := by
    rw [leWe_succ E]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
  have e1 : ∀ p, p = Om (1 + 1) * (E + 1) → ω ^ p * (b / ω ^ p) = β := by
    rintro p rfl
    obtain ⟨q, hq⟩ := hdv
    show leWe (E + 1) * (b / leWe (E + 1)) = β
    rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hlt1, add_zero]
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    rwa [e1 _ rfl] at h
  -- the domain facts
  have hED : VbD S l E := by
    refine ⟨(kjEfrom hdv hγ0 hγ2 hbD.1).1, (kjEfrom hdv hγ0 hγ2 hbD.2.1).1, ?_⟩
    refine lt_of_le_of_lt ?_ hbD.2.2
    refine ((Ordinal.right_le_opow E one_lt_omega0).trans (opow_le_opow_right omega0_pos
      (Ordinal.le_mul_right E ldOm2_SC.1))).trans ?_
    exact (Ordinal.le_mul_left (leWe E) (pos_iff_ne_zero.2 hγ0)).trans le_add_self
  have hE'D : VbD S l E' :=
    ⟨mem_of_add_one_mem hED.1, mem_of_add_one_mem hED.2.1, (lt_add_one E').trans hED.2.2⟩
  have hβD : VbD S l β := by
    have h1 := (Vh.vhC_div _ hbD.1 (Om (1 + 1) * (E + 1))).1
    have h2 := (Vh.vhC_div _ hbD.2.1 (Om (1 + 1) * (E + 1))).1
    rw [e1 _ rfl] at h1 h2
    exact ⟨h1, h2, le_self_add.trans_lt hbD.2.2⟩
  have hE1W : E + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hED.2.2
  have hWE1 : leWe (E + 1) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE1W).1
  have hE'1W : E' + 1 < Om ω := hED.2.2
  have hWE : leWe E < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE'1W).1
  have hWγ' : leWe E * γ' < leWe (E + 1) := by
    rw [leWe_succ E]; exact mul_lt_mul_of_pos_left hγ'2 (leWe_pos E)
  have hβ'D : VbD S l β' :=
    ⟨CSet.add_mem hβD.1 (leMulWe_mem hED.1 hγ'H), CSet.add_mem hβD.2.1 (leMulWe_mem hED.2.1
      (CSet.of_lt ((lt_add_one γ').trans hγθ))), vkOmW.1.isPrincipal hβD.2.2 (hWγ'.trans hWE1)⟩
  -- the context `G(v) = β' + W^{E'}·v`
  set t := KaT.base β' (Om (1 + 1) * E') with htdef
  have hGv : ∀ v, t.ev v = β' + leWe E' * v := fun v => rfl
  have hGΩ : t.ev (Om (1 + 1)) = b := by
    rw [hGv, ← leWe_succ, hbdef, mul_add_one, ← add_assoc]
  have hGm : Monotone t.ev := KaT.ev_mono t
  have hGlt : ∀ v, v < Om (1 + 1) → t.ev v < b := fun v hv => by
    rw [← hGΩ, hGv, hGv]
    exact (add_lt_add_iff_left β').2 (mul_lt_mul_of_pos_left hv (leWe_pos E'))
  have hown : ∀ v, v < S.psi b (Om (1 + 1)) → v < S.psi (t.ev v) (Om (1 + 1)) := fun v hv =>
    ktOwnTw t v (by rwa [hGΩ])
  have hβm : β ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
    CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hβn
  have hβ'm : β' ∈ S.CSet b (S.psi b (Om (1 + 1))) := CSet.add_mem hβm (leMulWe_mem hEγ.1 hγ'm)
  have hGmb : ∀ v, v ∈ S.CSet b (S.psi b (Om (1 + 1))) → t.ev v ∈ S.CSet b (S.psi b (Om (1 + 1))) :=
    fun v hv => by rw [hGv]; exact CSet.add_mem hβ'm (leMulWe_mem hE'm hv)
  -- the iterates and the stages
  set x0 := S.psi (t.ev 0) (Om (1 + 1)) with hx0def
  have h0 : x0 ≤ kgX S (Om (1 + 1)) t.ev x0 1 := by
    rw [kgX_succ, kgX_zero]; exact (psi_mono hκ2 (hGm zero_le)).1
  have hx0 : x0 < Om (1 + 1) := psi_lt hκ2 _
  have hgapD : ∀ n, KgGap (Om (1 + 1)) t.ev
      (S.CSet (t.ev (kgX S (Om (1 + 1)) t.ev x0 n)) (kgX S (Om (1 + 1)) t.ev x0 (n + 1)))
      (kgX S (Om (1 + 1)) t.ev x0 (n + 1)) := fun n => ktG_KaT (ktCl_CSet hκ2 _) t
  have hplat := kgPlat (S := S) hκ2 hGm h0 hx0 (fun a b => mxOm2_mem a b) hgapD
  have hstage : ∀ y ∈ S.CSet b (S.psi b (Om (1 + 1))),
      ∃ n, y ∈ S.CSet (t.ev (kgX S (Om (1 + 1)) t.ev x0 n)) (kgX S (Om (1 + 1)) t.ev x0 (n + 1)) := by
    intro y hy
    refine kgKey (S := S) hκ2 hGm h0 hx0 hgapD y ?_
    rw [hGΩ]
    exact CSet_mono le_rfl (by rw [← hGΩ]; exact hplat) hy
  set x := kgX S (Om (1 + 1)) t.ev x0 with hxdef
  have hxmono : Monotone x := monotone_nat_of_le_succ (kgX_mono hκ2 hGm h0)
  have hGhull : ∀ v, v ∈ cdHull S l → t.ev v ∈ cdHull S l := fun v hv => by
    rw [hGv]; exact CSet.add_mem hβ'D.1 (leMulWe_mem hE'D.1 hv)
  have hxlt : ∀ n, x n < S.psi b (Om (1 + 1)) ∧ GxCl (upsilon l) (ldAtR S l) (x n) := by
    have hat : ∀ v, v ∈ cdHull S l → v < Om (1 + 1) → v ∈ S.CSet b (S.psi b (Om (1 + 1))) →
        S.psi (t.ev v) (Om (1 + 1)) < S.psi b (Om (1 + 1)) ∧
          GxCl (upsilon l) (ldAtR S l) (S.psi (t.ev v) (Om (1 + 1))) := fun v hvH hv2 hvm => by
      refine ⟨psi_lt_psi_of_mem hκ2 (hGlt v hv2) (hGmb v hvm), GxCl.atom ⟨t.ev v, hGhull v hvH, ?_, rfl⟩⟩
      exact ((hGlt v hv2).trans hbD.2.2).trans_le (ConjT.OmW_le_A S _)
    intro n
    induction n with
    | zero =>
      exact hat 0 (CSet.zero_mem _ _) (lt_of_le_of_lt zero_le hx0) (CSet.zero_mem _ _)
    | succ n ih =>
      have hn2 : x n < Om (1 + 1) := ih.1.trans (psi_lt hκ2 _)
      exact hat (x n) ((ldHull_iff hl hX hn2).2 ih.2) hn2 (CSet.of_lt ih.1)
  -- the constants of `G` in a stage, so `G(v)` normal for `v ≥ x_N`
  obtain ⟨n₁, h₁⟩ := hstage E' hE'm
  obtain ⟨n₂, h₂⟩ := hstage γ' hγ'm
  set N := max n₁ n₂ with hNdef
  set v₀ := x N with hv₀def
  have hst : ∀ n, n ≤ N → ∀ v, v₀ ≤ v → v < Om (1 + 1) →
      S.CSet (t.ev (x n)) (x (n + 1)) ⊆ S.CSet (t.ev v) (S.psi (t.ev v) (Om (1 + 1))) := by
    intro n hn v hv _
    have hnv : x n ≤ v := (hxmono hn).trans hv
    exact CSet_mono (hGm hnv) (by rw [hxdef, kgX_succ]; exact (psi_mono hκ2 (hGm hnv)).1)
  have hnorm : ∀ v, v₀ ≤ v → v < S.psi b (Om (1 + 1)) →
      t.ev v ∈ S.CSet (t.ev v) (S.psi (t.ev v) (Om (1 + 1))) := by
    intro v hv hvb
    have hv2 : v < Om (1 + 1) := hvb.trans (psi_lt hκ2 _)
    have hE' := hst n₁ (le_max_left _ _) v hv hv2 h₁
    have hγ' := hst n₂ (le_max_right _ _) v hv hv2 h₂
    have hβ := CSet_mono (show β ≤ t.ev v from by rw [hGv]; exact le_self_add.trans le_self_add)
      (psi_mono hκ2 (show β ≤ t.ev v from by rw [hGv]; exact le_self_add.trans le_self_add)).1 hβn
    rw [hGv]
    exact CSet.add_mem (CSet.add_mem hβ (leMulWe_mem (CSet.succ_mem hE') hγ'))
      (leMulWe_mem hE' (CSet.of_lt (hown v hvb)))
  -- the image
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hZρ).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  set L := (KaT.base (vbT S l β') (Om 1 * vbT S l E')).ev with hLdef
  have hbθ : S.psi b (Om (1 + 1)) < ConjT.th S := psi_lt_psi_of_mem hκ2 hbD.2.2 hbD.2.1
  have hTG : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < S.psi b (Om (1 + 1)) →
      VbD S l (t.ev v) ∧ vbT S l (t.ev v) = L (gxTh (upsilon l) (ldAtR S l) v) := by
    intro v hv hvb
    have hv2 : v < Om (1 + 1) := hvb.trans (psi_lt hκ2 _)
    have hvH : v ∈ cdHull S l := (ldHull_iff hl hX hv2).2 hv
    have hvθ : v < ConjT.th S := hvb.trans hbθ
    have hWv : leWe E' * v < leWe E := by rw [hEdef, leWe_succ]; exact mul_lt_mul_of_pos_left hv2 (leWe_pos E')
    have hWvD : VbD S l (leWe E' * v) :=
      ⟨leMulWe_mem hE'D.1 hvH, leMulWe_mem hE'D.2.1 (CSet.of_lt hvθ), hWv.trans hWE⟩
    refine ⟨⟨by rw [hGv]; exact CSet.add_mem hβ'D.1 hWvD.1, by rw [hGv]; exact CSet.add_mem hβ'D.2.1 hWvD.2.1,
      by rw [hGv]; exact vkOmW.1.isPrincipal hβ'D.2.2 hWvD.2.2⟩, ?_⟩
    have h := Vh.vhT_cnfW hl hX hE'D (Xi.xiD_zero l) hvH hv2
    rw [add_zero, Vh.vhT_zero hl hX, add_zero] at h
    rw [hGv, Vh.vhT_add hl hX hβ'D hWvD, h]
    rfl
  have hTb : vbT S l b = L (Om 1) := by
    have hE1D : VbD S l E := hED
    obtain ⟨hWED, hWET⟩ := zxTW hl hX hE1D
    have hTE : vbT S l E = vbT S l E' + 1 := by rw [hEdef, Vh.vhT_add hl hX hE'D h1D, hT1]
    have hbeq : b = β' + leWe E := by rw [hbdef, mul_add_one, ← add_assoc]
    rw [hbeq, Vh.vhT_add hl hX hβ'D hWED, hWET, hTE, leOe_succ]
    rfl
  have hLm : Monotone L := KaT.ev_mono _
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) with hZdef
  have hZ : SC Z := gxTh_SC hZρ hAt (SC_psi hκ2 _) (hZρ1.trans (psiS_bounds (S := S) _ 1).1)
  have hgapT : KtGapY (vbT S l b) L
      {y | HCl S (A + 1 + S.psi (vbT S l b) (Om (1 + 1))) Z y} Z := by
    rw [hTb]; exact ktG_KaT (ktCl_HCl hZ) _
  have hv₀ : v₀ < S.psi b (Om (1 + 1)) := (hxlt N).1
  -- `Ω₃ ∣ G v`, `Ω₃ ≤ G v`
  have hW3 : leWe (Om (1 + 1 + 1)) = Om (1 + 1 + 1) := Vn.vnWe_Om3
  have hdv3E' : Om (1 + 1 + 1) ∣ leWe E' := by rw [← hW3]; exact leWe_dvd hE3
  have hdv3β : Om (1 + 1 + 1) ∣ β :=
    (hdv3E'.trans (leWe_dvd ((le_of_lt (lt_add_one E')).trans (le_of_lt (lt_add_one _))))).trans hdv
  have hdv3β' : Om (1 + 1 + 1) ∣ β' :=
    dvd_add hdv3β ((hdv3E'.trans (leWe_dvd (le_of_lt (lt_add_one E')))).trans (dvd_mul_right _ _))
  refine kuJump hl hX hA hρ hbD t.ev L hLm hgapT v₀ (hxlt N).2 hv₀ (fun v hvc hv hvb => ?_)
    (fun v v' hvc hv'c hv hvv' hv'b => ?_)
  · have hv2 : v < Om (1 + 1) := hvb.trans (psi_lt hκ2 _)
    obtain ⟨hGD, hGT⟩ := hTG v hvc hvb
    have hψ : S.psi (t.ev v) (Om (1 + 1)) < S.psi b (Om (1 + 1)) :=
      psi_lt_psi_of_mem hκ2 (hGlt v hv2) (hGmb v (CSet.of_lt hvb))
    have hv1 : (0 : Ordinal.{0}) < v := (SC_psi hκ2 _).1.trans_le
      (show x0 ≤ v from (hxmono (Nat.zero_le N)).trans hv)
    have hN : KuN S l (t.ev v) := by
      refine ⟨hGD, hnorm v hv hvb, ?_, ?_⟩
      · rw [hGv]; exact dvd_add hdv3β' (hdv3E'.trans (dvd_mul_right _ _))
      · rw [hGv]
        refine le_trans ?_ le_add_self
        exact (Ordinal.le_of_dvd (leWe_pos E').ne' hdv3E').trans (Ordinal.le_mul_left _ hv1)
    exact ⟨hGD, hψ, hGT, IH _ hN (hGlt v hv2)⟩
  · have hv'2 : v' < Om (1 + 1) := hv'b.trans (psi_lt hκ2 _)
    have hv2 : v < Om (1 + 1) := hvv'.trans hv'2
    obtain ⟨hGD, -⟩ := hTG v hvc (hvv'.trans hv'b)
    obtain ⟨hG'D, -⟩ := hTG v' hv'c hv'b
    have hGlt' : t.ev v < t.ev v' := by
      rw [hGv, hGv]; exact (add_lt_add_iff_left β').2 (mul_lt_mul_of_pos_left hvv' (leWe_pos E'))
    have hmem : t.ev v ∈ S.CSet (t.ev v') (S.psi (t.ev v') (Om (1 + 1))) :=
      CSet_mono hGlt'.le (psi_mono hκ2 hGlt'.le).1 (hnorm v hv (hvv'.trans hv'b))
    exact psi_lt_psi_of_mem hκ2 (vbT_mono hl hX hGD hG'D hGlt') (Xd.xdTr hl hX hG'D hGD hmem)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ku

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ku.kuSuccE
