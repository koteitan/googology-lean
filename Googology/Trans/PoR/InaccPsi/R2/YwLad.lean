import Googology.Trans.PoR.InaccPsi.R2.YwU

/-!
# YwLad: THE SUCCESSOR STEP AT A CLOSED TOP — THE LADDER WITH `e(x) ≤ E_K(x)`, AND THE LAYER OF `B_Γ + 1`

`Ge.GeqH B e` (the ladder over a gated base `B` up to the next base atom `ϑˣ(Ω₁·Ω₁ + e(x))`) asks `e(x) < E_K(x)`
strictly; at a top `E_K(x) = p` that is a fixed point of `ν ↦ Γ_{x+1+ν}` (the layer of `B_Γ`, `Yw.ywBGB`) the next
base atom is `ϑˣ(Ω₁·Ω₁ + p)`, so `e(x) = E_K(x)` and no `GeqH` exists.  Here `e(x) ≤ E_K(x)` suffices (`YwLH`, every
`GeqH` is one: `YwLH.ofGe`); the term system is that of `Ge.geqUSys` (the terms `Gd.GdT B` of the gated ladder), the
cofinality `ywL_lt_iff` is re-proved with `≤`, and the top witness comes from Lemma IMG (`Yw.ywTopWit`):

* `YwLH B e`, `YwLH.ofGe`, `ywL_gP_lt`, `ywL_lt_iff` (**`v < ϑˣ(Ω₁·Ω₁ + e(x))` iff `v` is below a ladder stage**),
  `ywLSys`, `ywLadL`, `ywLadB` (**THE LADDER LIMIT LAYER, top `ϑˣ(Ω₁·Ω₁ + e(x))`**, same gate);
* `ywBG1H`, `ywBG1B` (**THE LAYER OF THE CODE `B_Γ + 1`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + D(x))`, `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`,
  the next base atom above the first fixed point), `ywBG1B_E`.

No new axiom.  New definitions: `YwLH`, `ywLSys`, `ywLadL`, `ywLadB`, `ywBG1H`, `ywBG1B`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gm

/-- **The ladder hypothesis with `e(x) ≤ E_K(x)`**: `e(x) ∈ Tˣ ∩ Ω₁`, `e(x) ≤ E_K(x)`, every base atom
`ϑˣ(Ω₁·Ω₁ + j)`, `j < e(x)`, at most `E_K(x)`, `E_K(x) < ϑˣ(Ω₁·Ω₁ + e(x)) < X^x`, Lemma EXACT for `e`. -/
structure YwLH (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) : Prop where
  mem : ∀ x, InE x → x < Om1 → B.g < x → e x ∈ Tset x ∧ e x < Om1
  ele : ∀ x, InE x → x < Om1 → B.g < x → e x ≤ B.K.E x
  lo : ∀ x, InE x → x < Om1 → B.g < x → ∀ j, j ∈ Tset x → j < e x → gq j x ≤ B.K.E x
  hi : ∀ x, InE x → x < Om1 → B.g < x → B.K.E x < gq (e x) x
  X : ∀ x, InE x → x < Om1 → B.g < x → gq (e x) x < ywX x
  pi : ∀ σ ρ, Bases σ ρ → B.g < σ → e ρ ∈ TB ρ σ ∧ pi σ ρ (e ρ) = e σ

variable {B : GdB}

/-- **Every `Ge.GeqH` whose top is below `X^x` is a `YwLH`.** -/
theorem YwLH.ofGe {e : Ordinal.{0} → Ordinal.{0}} (H : GeqH B e)
    (hX : ∀ x, InE x → x < Om1 → B.g < x → gq (e x) x < ywX x) : YwLH B e :=
  ⟨H.mem, fun x hx hx1 hg => (H.elt x hx hx1 hg).le, H.lo, H.hi, hX, H.pi⟩

section Lim

variable {e : Ordinal.{0} → Ordinal.{0}} (H : YwLH B e)
include H

theorem YwLH.facts {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    gq (e x) x ∈ Tset x ∧ x < gq (e x) x ∧ gq (e x) x < Om1 ∧ InE (gq (e x) x) ∧ Indec (gq (e x) x) :=
  geq_facts hx hx1 (H.mem x hx hx1 hg).1 (H.mem x hx hx1 hg).2

theorem ywL_gP_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) : ∀ n : ℕ, gdP B n x < gq (e x) x
  | 0 => H.hi x hx hx1 hg
  | n + 1 => by
      obtain ⟨hgT, -, hg1, -⟩ := gdP_facts B hx hx1 hg n
      obtain ⟨hkT, hk1⟩ := H.mem x hx hx1 hg
      have ih := ywL_gP_lt hx hx1 hg n
      have h := lgVt_lt_low hx hx1 hgT hg1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hkT hk1 ih
        (hx.pos.trans (H.facts hx hx1 hg).2.1)
      rw [add_zero] at h
      exact h

/-- **`v < ϑˣ(Ω₁·Ω₁ + e(x))` iff `v < gdP B n x` for some `n`** (above the gate; `e(x) ≤ E_K(x)`). -/
theorem ywL_lt_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ v, v < gq (e x) x → ∃ n, v < gdP B n x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := H.facts hx hx1 hg
  obtain ⟨hkT, hk1⟩ := H.mem x hx hx1 hg
  have hEP1 : B.K.E x < gdP B 1 x := gdP_lt_succ B hx hx1 hg 0
  have hxE := gdx_E_gt hx hx1 hg
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases le_or_gt v (B.K.E x) with hvE | hEv
  · exact ⟨1, hvE.trans_lt hEP1⟩
  have hxv : x < v := hxE.trans hEv
  have hv1 : v < Om1 := hv.trans hG1
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hGT hG1 hv.le
  by_cases hI : Indec v
  · by_cases hvE' : InE v
    · obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv.le hv1 hI
      have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv, by rw [hξv]; exact hvE'⟩
      have hξk : ξ < Om1 * Om1 + e x :=
        lgLt_of_vt_lt hx hx1 hξT hξ2 hkT hk1 (by rw [hξv]; exact (H.ele x hx hx1 hg).trans_lt hEv)
          (by rw [hξv]; exact hv)
      rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
      · obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
        have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
        have hqr : ξ / Om1 < v ∧ ξ % Om1 < v := by
          rcases lt_or_ge (ξ / Om1) x with hqx | hxq
          · have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rw [hdec, hξv] at h
            exact ⟨hqx.trans hxv, h⟩
          · have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
            have h := lvLevel_lt_vt hx hx1 hqT hxq hqΩ hrT hr1
            rw [hdec, hξv] at h
            exact h
        obtain ⟨n1, hn1⟩ := IH _ hqr.1 (hqr.1.trans hv)
        obtain ⟨n2, hn2⟩ := IH _ hqr.2 (hqr.2.trans hv)
        refine ⟨max n1 n2 + 1, ?_⟩
        have hq' : ξ / Om1 < gdP B (max n1 n2) x := hn1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _))
        have hr' : ξ % Om1 < gdP B (max n1 n2 + 1) x :=
          hn2.trans_le (gdP_mono B hx hx1 hg ((le_max_right _ _).trans (Nat.le_succ _)))
        rw [← hξv, ← hdec]
        exact gd_lt_top B hx hx1 hg hqT hq' hrT hr1 hr'
      · have hje : Om1 * Om1 + (ξ - Om1 * Om1) = ξ := Ordinal.add_sub_cancel_of_le hξs
        have hjk : ξ - Om1 * Om1 < e x := (add_lt_add_iff_left _).1 (by rw [hje]; exact hξk)
        obtain ⟨j, hj⟩ : ∃ j, j = ξ - Om1 * Om1 := ⟨_, rfl⟩
        have hvj : v = gq j x := by rw [← hξv, ← hje, ← hj]; rfl
        have hjT : j ∈ Tset x := vz_T_down hx hx1 hkT hk1 (hj ▸ hjk).le
        exact absurd (H.lo x hx hx1 hg j hjT (hj ▸ hjk)) (not_le.2 (hvj ▸ hEv))
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
        (fun h => hvE' (by unfold InE; rw [← h]; exact h.symm))
      obtain ⟨n, hn⟩ := IH L hL (hL.trans hv)
      exact ⟨n, (gdP_facts B hx hx1 hg n).2.2.2.opow_lt hn⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_le_of_lt zero_le hxv).ne'
    obtain ⟨n1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨n2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    refine ⟨max n1 n2, ?_⟩
    rw [← hsum]
    exact (inE_indec (gdP_facts B hx hx1 hg _).2.2.2).add_lt
      (h1.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _)))
      (h2.trans_le (gdP_mono B hx hx1 hg (le_max_right _ _)))

theorem ywL_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hg : B.g < upsilon l) :
    gq (e (upsilon l)) (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  obtain ⟨hkT, hk1⟩ := H.mem _ (ups_inE hl) (ups_lt_Om1 l hl1) hg
  exact (geq_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) hkT hk1 (upsilon_normal.strictMono h1)
    hτU.2).trans (upsilon_normal.strictMono (lt_add_one _))

end Lim

/-- **The ladder term system over the gated base** (the terms of `Gd.GdT B`), top `ϑˣ(Ω₁·Ω₁ + e(x))`. -/
noncomputable def ywLSys (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : YwLH B e) : GdSys B.g where
  Tm := GdT B
  val := GdT.val
  CB := GdT.CBt
  cs := GdT.cs
  cst := GdT.cst
  top := fun x => gq (e x) x
  cb_cst := fun _ _ h => GdT.cbt_cst h
  cb_iff := fun _ _ _ h hc => GdT.cbt_iff h hc
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 hg t hCB =>
    (GdT.gd_T (ups_inE hl) (ups_lt_Om1 l hl1) hg t hCB).2.trans
      (ywL_gP_lt H (ups_inE hl) (ups_lt_Om1 l hl1) hg _)
  one_le_top := fun l hl hl1 hg =>
    one_le_iff_pos.2 (H.facts (ups_inE hl) (ups_lt_Om1 l hl1) hg).2.2.2.1.pos
  rep := fun l hl hl1 hg v hv => by
    obtain ⟨n, hn⟩ := ywL_lt_iff H (ups_inE hl) (ups_lt_Om1 l hl1) hg v hv
    obtain ⟨t, h1, -, h3⟩ :=
      gd_rep (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)) (ups_lt_Om1 l hl1) hg (gdxRep_ri hl hl1 hg) n v hn
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 hg => ywL_lt_next_ups H hl hl1 hg
  pkg := fun _ hl hl1 hg _ hCB h1 R => GdGK.pkgGd R hg (gdxRep_ri hl hl1 hg) (gdxBase_ri hl hl1 hg R) hCB h1
  rs := fun _ _ _ hg _ hCB => rsStep_Gd hg hCB
  uni_le := fun _ _ hσ hρ hB hg _ _ ht hu => GdT.uni_le hσ hρ hB hg ht hu
  small := gd_small

/-- **The ladder limit layer** with top `ϑˣ(Ω₁·Ω₁ + e(x))`; the top witness from Lemma IMG (`Yw.ywTopWit`). -/
noncomputable def ywLadL (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : YwLH B e) : GdLay B.g where
  sys := ywLSys B e H
  E := fun x => gq (e x) x
  top_eq := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg =>
    opow_dvd_of_inE (H.facts hx hx1 hg).2.2.2.1 (H.facts hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (H.facts hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu =>
    geq_lt_next hx hx1 (H.mem x hx hx1 hg).1 (H.mem x hx hx1 hg).2 hxu hu.2
  lt_top_E := fun x hx hx1 hg t ht => (GdT.gd_T hx hx1 hg t ht).2.trans (ywL_gP_lt H hx hx1 hg _)
  exact := fun _ _ hσ hρ hB hg t ht => GdT.pi hσ hρ hB hg t ht
  exp_pi := fun σ ρ _ _ hB hg => geq_pi hB (H.pi σ ρ hB hg)
    (H.mem ρ hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1)).2
  top_wit := fun _ _ _ h hg => by
    have hρE := upsPt_inE h.ρU
    obtain ⟨-, hρG, -, hGE, -⟩ := H.facts hρE h.ρ1 hg
    exact ywTopWit h (T := fun x => gq (e x) x) hg hGE hρG (H.X _ hρE h.ρ1 hg)
      (fun σ _ hB hgσ => (geq_pi hB (H.pi σ _ hB hgσ) (H.mem _ hρE h.ρ1 hg).2).2)

/-- **The ladder limit base package** (same gate). -/
noncomputable def ywLadB (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : YwLH B e) : GdB where
  g := B.g
  K := ywLadL B e H
  ek := fun x hx hx1 hg => (H.facts hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (H.facts hx hx1 hg).1

theorem ywLadB_E (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : YwLH B e) (x : Ordinal.{0}) :
    (ywLadB B e H).K.E x = gq (e x) x := rfl

theorem ywLadB_g (B : GdB) (e : Ordinal.{0} → Ordinal.{0}) (H : YwLH B e) : (ywLadB B e H).g = B.g := rfl

/-! ## The layer of `B_Γ + 1` -/

/-- **The ladder hypothesis over the layer of `B_Γ`** with `e = D = ϑˣ(Ω₁·Ω₁ + Ω₁)` (`e(x) = E_K(x)`). -/
theorem ywBG1H : YwLH ywBGB (fun x => ywV 1 0 x) := by
  refine ⟨fun x hx hx1 _ => ?_, fun x _ _ _ => le_rfl, fun x hx hx1 _ j hjT hj => ?_, fun x hx hx1 _ => ?_,
    fun x hx hx1 _ => ?_, fun σ ρ hB _ => ?_⟩
  · obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
    exact ⟨hDT, (ywD_lt_X hx hx1).trans (ywX_facts hx hx1).2.2.1⟩
  · exact ((ywD_closed hx hx1).2.2 j hjT hj).le
  · obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
    exact gmq_gt hx hx1 hDT ((ywD_lt_X hx hx1).trans (ywX_facts hx hx1).2.2.1)
  · obtain ⟨-, hDT, -⟩ := ywD_closed hx hx1
    rw [← ywV_zero]
    have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
    obtain ⟨-, hxX, hX1, -⟩ := ywX_facts hx hx1
    exact ywV_lt_X hx hx1 h0T (hx.pos.trans hx1) hDT ((ywD_lt_X hx hx1).trans hX1) (hx.pos.trans hxX)
      (ywD_lt_X hx hx1)
  · have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
    have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
    have h1 := ywV_pi hB (mem_TB_of_lt hB h1σ) ((lu_one_lt_E hB.2.1).trans hB.2.2.2) (mem_TB_of_lt hB h0σ)
      (hB.2.1.pos.trans hB.2.2.2)
    rw [pi_lt hB h1σ, pi_lt hB h0σ] at h1
    exact h1

/-- **THE LAYER OF THE CODE `B_Γ + 1`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + D(x))` (`D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`), the ladder limit
over the layer of `B_Γ`. -/
noncomputable def ywBG1B : GdB := ywLadB ywBGB (fun x => ywV 1 0 x) ywBG1H

theorem ywBG1B_g : ywBG1B.g = 0 := rfl

theorem ywBG1B_E (x : Ordinal.{0}) : ywBG1B.K.E x = gq (ywV 1 0 x) x := rfl

end Googology.Trans.PoR.InaccPsi.R2.Yw
