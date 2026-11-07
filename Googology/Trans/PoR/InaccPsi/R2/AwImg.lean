import Googology.Trans.PoR.InaccPsi.R2.AwRS
import Googology.Trans.PoR.InaccPsi.R2.XiImg

/-!
# AwImg: LEMMA IMG AT THE READINGS OF THE CODES BELOW `K_ω`

In a restart context `RstK ρ τ δ` and for a copy `f` (`ImgCtx ρ A f`, `σ = f ρ`), Lemma IMG at a code `c` says
`Θ_σ(c) ≤ f(Θ_ρ(c))`.  Below `θ` this is `Xi.xi_img_all` with `Θ = R` (`Xi.xiR_pi`).  At `θ`, `Θ_ρ(θ) = x` is the next `υ`-point,
`x ≤₁ τ`, `f(τ)` is a `υ`-point (`ImgCtx.pinU`), so `f(x)` is a `υ`-point above `σ`: `x' = Θ_σ(θ) ≤ f(x)`.  Sums and `ω`-powers go as
`Gn.gnI_add`, `Gn.gnI_succ`, `Gn.gnI_lim`, with `Θ` for `π`.  At an `ε`-number `e = Θ_ρ(c)` the sets `X`, `Z` of [W07b] Claim 5.6 at
the greatest `<₁`-predecessor `τ'` of `e` in `[x, e)` and the FRAG map `Ψ` from `(σ, x')` to `(ρ, x)` over an `ε`-number `κ < σ`
(`Aw.aw_can`: `Ψ(Θ_σ z) = Θ_ρ z`) give the covering `h = Ψ ∘ f`: if `f(e) < Θ_σ(c)` then `h(e) < e`, `X ≤pw h[X]`, and
`h[Z] < e` because `h(e) ≤₁ h(l)` with `h(l) ≥ e` would put `h(e)` at most at `τ'`.

* `AwI`, `aw_fx` (`x' ≤ f(x)`), `aw_ups_big`;
* `aw_opow_code`, `aw_dvd`, `aw_lg_parts`;
* `awI_low` (below `θ`), `awI_th`, `awI_add`, `awI_succ`, `awI_lim`, `aw_base`, `awI_eps`, `aw_img` (**LEMMA IMG AT EVERY CODE BELOW `K_ω`**),
  `aw_pkg` (**THE IMG PACKAGE**).

No new axiom (it uses `R2.claim56pw`).  New definition: `AwI`.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Zk Googology.Trans.PoR.InaccPsi.R2.Xj Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Lemma IMG at the code `c`**: witness sets containing `Θ_ρ(c)`; every copy `f` of a set containing them has `c` a code over `f(ρ)`
and `Θ_{f(ρ)}(c) ≤ f(Θ_ρ(c))`. -/
def AwI (S : InaccSeq.{0}) (ρ δ c : Ordinal.{0}) : Prop :=
  ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gxTh ρ (awAt S ρ) c ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      GxCl (f ρ) (awAt S (f ρ)) c ∧ gxTh (f ρ) (awAt S (f ρ)) c ≤ f (gxTh ρ (awAt S ρ) c)

section Codes

variable {y : Ordinal.{0}} (hy : SC y)
include hy

theorem aw_opow_code {a : Ordinal.{0}} (h : GxCl y (awAt S y) (ω ^ a)) : GxCl y (awAt S y) a := by
  have := (gxDec hy (aw_gxAt S y) _ h).2
  rwa [log_opow one_lt_omega0] at this

/-- `ω^z ∣ a` for codes gives `ω^{Θ z} ∣ Θ a`. -/
theorem aw_dvd {z : Ordinal.{0}} (hz : GxCl y (awAt S y) z) : ∀ a, GxCl y (awAt S y) a → ω ^ z ∣ a →
    ω ^ gxTh y (awAt S y) z ∣ gxTh y (awAt S y) a := by
  refine zk_ind (fun _ _ => by rw [gxTh_zero]; exact dvd_zero _) ?_
  intro c k r hk0 hk hr IH ha hd
  obtain ⟨hcc, hrc⟩ := aw_parts_code hy hk0 hk hr ha
  obtain ⟨e1, e2⟩ := aw_Rd_cnf hy hk hcc hrc hr
  have hzc : z ≤ c := by
    by_contra hlt
    push Not at hlt
    have hne : ω ^ c * k + r ≠ 0 := (zk_parts hk0 hk hr).1
    have h1 : ω ^ z ≤ ω ^ c * k + r := Ordinal.le_of_dvd hne hd
    have h2 : ω ^ c * k + r < ω ^ (c + 1) := by
      rw [opow_add, opow_one]
      obtain ⟨n, rfl⟩ := lt_omega0.1 hk
      calc ω ^ c * (n : Ordinal.{0}) + r < ω ^ c * (n : Ordinal.{0}) + ω ^ c := (add_lt_add_iff_left _).2 hr
        _ = ω ^ c * ((n : Ordinal.{0}) + 1) := (mul_add_one _ _).symm
        _ ≤ ω ^ c * ω := mul_le_mul_right (by exact_mod_cast (nat_lt_omega0 (n + 1)).le) _
    exact absurd (h1.trans_lt h2) (not_lt.2 ((opow_le_opow_iff_right one_lt_omega0).2 (Order.add_one_le_of_lt hlt)))
  have hdk : ω ^ z ∣ ω ^ c * k := (opow_dvd_opow ω hzc).trans (dvd_mul_right _ _)
  have hdr : ω ^ z ∣ r := (Ordinal.dvd_add_iff hdk).1 hd
  rw [e1]
  have h3 : ω ^ gxTh y (awAt S y) z ∣ ω ^ gxTh y (awAt S y) c * k :=
    (opow_dvd_opow ω (gxTh_mono hzc)).trans (dvd_mul_right _ _)
  exact dvd_add h3 (IH hrc hdr)

/-- **The last term of a code**: `a = a' + ω^z`, `ω^z ∣ a'`, with `a'`, `z` codes. -/
theorem aw_lg_parts : ∀ a, a ≠ 0 → GxCl y (awAt S y) a → ∃ a' z, GxCl y (awAt S y) a' ∧ GxCl y (awAt S y) z ∧
    a = a' + ω ^ z ∧ ω ^ z ∣ a' ∧ a' < a ∧ z ≤ a := by
  refine zk_ind (fun h0 _ => absurd rfl h0) ?_
  intro c k r hk0 hk hr IH h0 ha
  obtain ⟨hcc, hrc⟩ := aw_parts_code hy hk0 hk hr ha
  have hcle : c ≤ ω ^ c * k + r :=
    (right_le_opow c one_lt_omega0).trans ((Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add)
  rcases eq_or_ne r 0 with rfl | hr0
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
      have : n ≠ 0 := fun e => hk0 (by simp [e])
      omega⟩
    refine ⟨ω ^ c * (m : Ordinal.{0}), c, aw_mul_nat hy (hcc.opow hy.1) m, hcc, ?_, dvd_mul_right _ _, ?_, hcle⟩
    · rw [add_zero, Nat.cast_succ, mul_add_one]
    · rw [add_zero, Nat.cast_succ, mul_add_one]
      exact lt_add_of_pos_right _ (opow_pos c omega0_pos)
  obtain ⟨r', z, hr'c, hzc, e, hd, hr'r, hzr⟩ := IH hr0 hrc
  have hzc' : z ≤ c := by
    have h1 : ω ^ z ≤ r := by rw [e]; exact le_add_self
    by_contra hlt
    push Not at hlt
    have h2 : ω ^ c ≤ ω ^ z := (opow_le_opow_iff_right one_lt_omega0).2 hlt.le
    exact absurd (h2.trans h1) (not_le.2 hr)
  refine ⟨ω ^ c * k + r', z, ?_, hzc, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    exact GxCl.add (aw_mul_nat hy (hcc.opow hy.1) n) hr'c
  · rw [add_assoc, ← e]
  · exact dvd_add ((opow_dvd_opow ω hzc').trans (dvd_mul_right _ _)) hd
  · exact (add_lt_add_iff_left _).2 hr'r
  · exact (hzr.trans le_add_self)

end Codes

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hρS : SC ρ)
include h hρS

theorem aw_x_facts : ρ < awNx ρ ∧ awNx ρ < τ ∧ UpsPt (awNx ρ) ∧ awNx (awNx ρ) < τ := by
  obtain ⟨hρx, hxU, hxS, hx1, -, hxn⟩ := awNx_facts hρS h.ρ1
  obtain ⟨hxm, hmU, -, -, -, hmn⟩ := awNx_facts hxS hx1
  obtain ⟨u, huU, hρu, huτ⟩ := h.cof ρ h.ρτ
  have hxτ : awNx ρ < τ := (hxn.2.2 u hρu huU).trans_lt huτ
  obtain ⟨u', huU', hxu', huτ'⟩ := h.cof _ hxτ
  exact ⟨hρx, hxτ, hxU, (hmn.2.2 u' hxu' huU').trans_lt huτ'⟩

omit hρS in
theorem aw_σ_facts (S : InaccSeq.{0}) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) :
    f ρ < ρ ∧ f ρ < Om1 ∧ SC (f ρ) ∧ InE (f ρ) := by
  have hfρ : f ρ < ρ := C.low _ C.rho
  have h1 : f ρ < Om1 := hfρ.trans h.ρ1
  have hS : SC (f ρ) := aw_ups_SC S C.ups h1
  exact ⟨hfρ, h1, hS, upsPt_inE C.ups⟩

/-- **`f(x)` is a `υ`-point**: `x ≤₁ τ` and `f(τ)` is a `υ`-point. -/
theorem aw_fx_ups {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) (hxA : awNx ρ ∈ A) (hτA : τ ∈ A) :
    UpsPt (f (awNx ρ)) := by
  obtain ⟨hρx, hxτ, hxU, -⟩ := aw_x_facts h hρS
  have hle : le1 (awNx ρ) τ := (h.lowδ _ _ hρx h.τδ.le).2 (hxU.2 τ hxτ.le)
  have hcov := C.cov1 _ hxA _ hτA hle
  have hfτ := C.pinU τ δ h
  have hlt : f (awNx ρ) < f τ := C.mono hxA hτA hxτ
  have hσx : f ρ < f (awNx ρ) := C.mono C.rho hxA hρx
  by_contra hU
  have hR := (C.sk _ (C.low _ hxA) hU _).1 hcov
  exact hU ⟨lt_of_le_of_lt zero_le hσx, (le1R_lt_ups hfτ hlt le_rfl).1 hR⟩

/-- **`x' ≤ f(x)`.** -/
theorem aw_fx (S : InaccSeq.{0}) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) (hxA : awNx ρ ∈ A)
    (hτA : τ ∈ A) : awNx (f ρ) ≤ f (awNx ρ) := by
  obtain ⟨hρx, -, -, -⟩ := aw_x_facts h hρS
  obtain ⟨hfρ, hσ1, hσS, -⟩ := aw_σ_facts (S := S) h C
  exact (awNx_facts hσS hσ1).2.2.2.2.2.2.2 _ (C.mono C.rho hxA hρx) (aw_fx_ups h hρS C hxA hτA)

/-- A copy that is a `υ`-point above `f(x)` lies above every reading at `f(ρ)`. -/
theorem aw_ups_big {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) (hxA : awNx ρ ∈ A) (hτA : τ ∈ A)
    {v c : Ordinal.{0}} (hvA : v ∈ A) (hxv : awNx ρ < v) (hU : UpsPt (f v)) (hc : GxCl (f ρ) (awAt S (f ρ)) c) :
    gxTh (f ρ) (awAt S (f ρ)) c < f v := by
  obtain ⟨hfρ, hσ1, hσS, -⟩ := aw_σ_facts (S := S) h C
  have h1 : awNx (f ρ) < f v := (aw_fx h hρS S C hxA hτA).trans_lt (C.mono hxA hvA hxv)
  obtain ⟨-, -, hxS, hx1, -, -⟩ := awNx_facts hσS hσ1
  exact (aw_Rd_lt hσS hσ1 hc).trans_le ((awNx_facts hxS hx1).2.2.2.2.2.2.2 _ h1 hU)

/-- The pieces of an `AwI` inside a copy. -/
theorem awI_use {c : Ordinal.{0}} (hI : AwI S ρ δ c) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gxTh ρ (awAt S ρ) c ∈ W ∪ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        gxTh ρ (awAt S ρ) c ∈ A ∧ GxCl (f ρ) (awAt S (f ρ)) c ∧ gxTh (f ρ) (awAt S (f ρ)) c ≤ f (gxTh ρ (awAt S ρ) c) := by
  obtain ⟨W, Z, w, m, b⟩ := hI
  exact ⟨W, Z, w, m, fun A f hW hZ C => ⟨mem_A m hW hZ, b A f hW hZ C⟩⟩

/-- The base witness set `{x, τ}`. -/
theorem aw_wz0 : WZ ρ δ {awNx ρ, τ} ∅ := by
  obtain ⟨hρx, hxτ, hxU, -⟩ := aw_x_facts h hρS
  have := ((WZ.empty (ρ := ρ) (δ := δ)).insW h.ρτ.le h.τδ (Or.inl (indec_of_upsPt h.τU))).insW hρx.le
    (hxτ.trans h.τδ) (Or.inl (indec_of_upsPt hxU))
  simpa using this

/-- **Below `θ`** (`Xi.xi_img_all`). -/
theorem awI_low {c : Ordinal.{0}} (hcθ : c < ConjT.th S) (hc : GxCl ρ (awAt S ρ) c) : AwI S ρ δ c := by
  classical
  have hρ1 := h.ρ1
  have hρE : InE ρ := h.ρE
  have hd : WDom S ρ c := (xi_dom_codes hρS hρ1 hcθ).1 ((aw_code_th hcθ).1 hc)
  rcases hd with hcρ | ⟨hc1, -, hP⟩
  · refine ⟨∅, {c}, WZ.empty.insZ hcρ, ?_, fun A f _ hZ C => ?_⟩
    · rw [gxTh_small hcρ.le]; simp
    · have hcA : c ∈ A := hZ (by simp)
      have hcσ : c < f ρ := C.above c hcA hcρ
      rw [gxTh_small hcρ.le, gxTh_small hcσ.le, C.fix c hcA hcρ]
      exact ⟨GxCl.small hcσ, le_rfl⟩
  have hd : WDom S ρ c := Or.inr ⟨hc1, hcθ, hP⟩
  obtain ⟨hRT, hR1⟩ := xiR_T S hρE hρ1 c hd
  obtain ⟨W, Z, w, hm, -, -, b⟩ := Gn.gnI_use h (xi_img_all h _ hRT hR1)
  have wzc : WZ ρ δ ∅ (wP c) := ⟨by simp, fun z hz => hP z hz, by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨W, Z ∪ wP c, hw', ?_, fun A f hW hZ C => ?_⟩
  · rw [aw_Rd_xi hρS hρ1 hd]
    rcases Finset.mem_union.1 hm with h1 | h1
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
  have hZA : ↑Z ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  obtain ⟨-, -, hle⟩ := b A f hW hZA C
  obtain ⟨hfρ, hσ1, hσS, hσE⟩ := aw_σ_facts (S := S) h C
  have hdf : WDom S (f ρ) c := Or.inr ⟨hc1, hcθ, fun p hp =>
    C.above p (hZ (Finset.mem_coe.2 (Finset.mem_union_right _ hp))) (hP p hp)⟩
  refine ⟨(aw_code_th hcθ).2 ((xi_dom_codes hσS hσ1 hcθ).2 hdf), ?_⟩
  rw [aw_Rd_xi hρS hρ1 hd, aw_Rd_xi hσS hσ1 hdf, ← (xiR_pi hσE hρE hfρ hρ1 c hdf).2]
  exact hle

/-- **At `θ`**: `Θ_σ(θ) = x' ≤ f(x)`. -/
theorem awI_th : AwI S ρ δ (ConjT.th S) := by
  classical
  refine ⟨_, _, aw_wz0 h hρS, ?_, fun A f hW _ C => ?_⟩
  · rw [aw_Rd_th hρS h.ρ1]; simp
  obtain ⟨hfρ, hσ1, hσS, -⟩ := aw_σ_facts (S := S) h C
  rw [aw_Rd_th hρS h.ρ1, aw_Rd_th hσS hσ1]
  exact ⟨GxCl.atom (aw_th_mem _), aw_fx h hρS S C (hW (by simp)) (hW (by simp))⟩

/-- **A sum.** -/
theorem awI_add {u v : Ordinal.{0}} (hu : GxCl ρ (awAt S ρ) u) (hv : GxCl ρ (awAt S ρ) v) (h1 : AwI S ρ δ u) (h2 : AwI S ρ δ v)
    (hu1 : u < u + v) (hv2 : v < u + v) (hρv : ρ ≤ gxTh ρ (awAt S ρ) (u + v)) : AwI S ρ δ (u + v) := by
  classical
  have hAt : GxAt (awAt S ρ) := aw_gxAt S ρ
  obtain ⟨W1, Z1, w1, m1, b1⟩ := awI_use h hρS h1
  obtain ⟨W2, Z2, w2, m2, b2⟩ := awI_use h hρS h2
  have e := gxTh_add hρS hAt hu v
  have hδ : gxTh ρ (awAt S ρ) (u + v) < δ := aw_lt_δ h hρS (GxCl.add hu hv)
  have hlt1 : gxTh ρ (awAt S ρ) u < gxTh ρ (awAt S ρ) (u + v) := gxTh_lt hu hu1
  have hlt2 : gxTh ρ (awAt S ρ) v < gxTh ρ (awAt S ρ) (u + v) := gxTh_lt hv hv2
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨_, _, (w1.union w2).insW hρv hδ (Or.inr ⟨_, hm _ (Or.inl m1), _, hm _ (Or.inr m2), hlt1, hlt2, e.symm⟩),
    by simp, fun A f hW hZ C => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨a1, c1, p1⟩ := b1 A f hW1 hZ1 C
  obtain ⟨a2, c2, p2⟩ := b2 A f hW2 hZ2 C
  have hvA : gxTh ρ (awAt S ρ) (u + v) ∈ A := hW (by simp)
  obtain ⟨-, -, hσS, -⟩ := aw_σ_facts (S := S) h C
  refine ⟨GxCl.add c1 c2, ?_⟩
  rw [gxTh_add hσS (aw_gxAt S _) c1 v]
  have := C.add _ a1 _ a2 _ hvA e.symm
  rw [← this]
  exact add_le_add p1 p2

/-- **`ω^{a+1}`** from `ω^a`. -/
theorem awI_succ {a : Ordinal.{0}} (ha : GxCl ρ (awAt S ρ) a) (hw : AwI S ρ δ (ω ^ a))
    (hρv : ρ ≤ gxTh ρ (awAt S ρ) (ω ^ (a + 1))) : AwI S ρ δ (ω ^ (a + 1)) := by
  classical
  have hAt : GxAt (awAt S ρ) := aw_gxAt S ρ
  have hS1 : GxCl ρ (awAt S ρ) 1 := aw_nat_code hρS (by simpa using nat_lt_omega0 1)
  have hc' : GxCl ρ (awAt S ρ) (ω ^ (a + 1)) := (GxCl.add ha hS1).opow hρS.1
  obtain ⟨W1, Z1, w1, m1, b1⟩ := awI_use h hρS hw
  have hδ := aw_lt_δ h hρS hc'
  have e1 : ∀ {y : Ordinal.{0}}, SC y → GxCl y (awAt S y) a →
      gxTh y (awAt S y) (ω ^ (a + 1)) = ω ^ (gxTh y (awAt S y) a + 1) := by
    intro y hy hay
    rw [gxTh_opow hy (aw_gxAt S y) (GxCl.add hay (aw_nat_code hy (by simpa using nat_lt_omega0 1))),
      gxTh_add hy (aw_gxAt S y) hay]
    rw [gxTh_small (Gg.gg_one_lt_of_SC hy).le]
  have hind : Indec (gxTh ρ (awAt S ρ) (ω ^ (a + 1))) := by
    rw [e1 hρS ha]; exact indec_opow _
  refine ⟨_, _, w1.insW hρv hδ (Or.inl hind), by simp, fun A f hW hZ C => ?_⟩
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  obtain ⟨aw, cw, pw⟩ := b1 A f hW1 hZ C
  obtain ⟨-, -, hσS, -⟩ := aw_σ_facts (S := S) h C
  have hAtσ : GxAt (awAt S (f ρ)) := aw_gxAt S _
  have haσ : GxCl (f ρ) (awAt S (f ρ)) a := aw_opow_code hσS cw
  have hvA : gxTh ρ (awAt S ρ) (ω ^ (a + 1)) ∈ A := hW (by simp)
  refine ⟨(GxCl.add haσ (aw_nat_code hσS (by simpa using nat_lt_omega0 1))).opow hσS.1, ?_⟩
  have hlt : f (gxTh ρ (awAt S ρ) (ω ^ a)) < f (gxTh ρ (awAt S ρ) (ω ^ (a + 1))) :=
    C.mono aw hvA (gxTh_lt (ha.opow hρS.1) ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one a)))
  obtain ⟨a0, ha0⟩ := indec_eq_opow (C.indec _ hvA hind)
  rw [e1 hσS haσ, ha0]
  rw [gxTh_opow hσS hAtσ haσ] at pw
  rw [ha0] at hlt
  have : gxTh (f ρ) (awAt S (f ρ)) a < a0 := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt pw hlt)
  exact (opow_le_opow_iff_right one_lt_omega0).2 (Order.add_one_le_of_lt this)

/-- **`ω^{a+ω^z}`** (`z > 0`, `ω^z ∣ a`, `θ < ω^{a+ω^z}`) from `z` and, for `a ≠ 0`, from `ω^a`. -/
theorem awI_lim {a z : Ordinal.{0}} (haC : GxCl ρ (awAt S ρ) a) (hzC : GxCl ρ (awAt S ρ) z) (hz0 : z ≠ 0) (hd : ω ^ z ∣ a)
    (hzI : AwI S ρ δ z) (hwI : a ≠ 0 → AwI S ρ δ (ω ^ a)) (hne : a + ω ^ z < ω ^ (a + ω ^ z))
    (hθ : ConjT.th S < ω ^ (a + ω ^ z)) : AwI S ρ δ (ω ^ (a + ω ^ z)) := by
  classical
  have hAt : GxAt (awAt S ρ) := aw_gxAt S ρ
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  obtain ⟨hρx, hxτ, hxU, hmτ⟩ := aw_x_facts h hρS
  have hzp : GxCl ρ (awAt S ρ) (ω ^ z) := hzC.opow hρS.1
  have hXc : GxCl ρ (awAt S ρ) (a + ω ^ z) := GxCl.add haC hzp
  have hvc : GxCl ρ (awAt S ρ) (ω ^ (a + ω ^ z)) := hXc.opow hρS.1
  set X' := gxTh ρ (awAt S ρ) a with hX'def
  set z' := gxTh ρ (awAt S ρ) z with hz'def
  have eX : gxTh ρ (awAt S ρ) (a + ω ^ z) = X' + ω ^ z' := by
    rw [gxTh_add hρS hAt haC, gxTh_opow hρS hAt hzC]
  have ev : gxTh ρ (awAt S ρ) (ω ^ (a + ω ^ z)) = ω ^ (X' + ω ^ z') := by
    rw [gxTh_opow hρS hAt hXc, eX]
  have hz'0 : z' ≠ 0 := by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.zero hρS.1) (pos_iff_ne_zero.2 hz0)
    rw [gxTh_zero] at this
    exact this.ne'
  have hd' : ω ^ z' ∣ X' := aw_dvd hρS hzC a haC hd
  have hX'0 : a ≠ 0 → X' ≠ 0 := fun ha0 => by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.zero hρS.1) (pos_iff_ne_zero.2 ha0)
    rw [gxTh_zero] at this
    exact this.ne'
  set X := X' + ω ^ z' with hXdef
  set v := ω ^ X with hvdef
  have hxv : awNx ρ < v := by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.atom (aw_th_mem _)) hθ
    rwa [aw_Rd_th hρS h.ρ1, ev] at this
  have hρv : ρ < v := hρx.trans hxv
  have hXv : X < v := by
    have := gxTh_lt hXc hne
    rwa [eX, ev] at this
  have hvδ : v < δ := by rw [← ev]; exact aw_lt_δ h hρS hvc
  have hX0 : X ≠ 0 := (lt_of_lt_of_le (opow_pos z' omega0_pos) le_add_self).ne'
  have hlgX : lg X = z' := Ge.lg_add_opow hd'
  have hzX : z' ≤ X := by rw [← hlgX]; exact lg_le hX0
  have hzv : z' < v := lt_of_le_of_lt hzX hXv
  have hvz : v + z' < δ := hδI.add_lt hvδ (hzv.trans hvδ)
  have hdX : ω ^ z' ∣ X := by rw [hXdef]; exact dvd_add hd' (dvd_refl _)
  have hsrc : le1 v (v + z') := Gn.gn_src h hX0 hz'0 hdX hzv.le hρv hvz.le
  -- `X' ≥ ρ` when `a ≠ 0`
  have hX'v' : a ≠ 0 → ρ ≤ ω ^ X' ∧ z' ≤ ω ^ X' ∧ ω ^ X' < v := by
    intro ha0
    have hX'n := hX'0 ha0
    have hzX' : z' ≤ X' := (le_lg_iff hX'n z').2 hd' |>.trans (lg_le hX'n)
    have hρX' : ρ ≤ X' := by
      by_contra hlt
      push Not at hlt
      have hwz : ω ^ z' ≤ X' := Ordinal.le_of_dvd hX'n hd'
      have hXρ : X < ρ := (inE_indec hρE).add_lt hlt (hwz.trans_lt hlt)
      have : v < ρ := by
        rw [hvdef, ← show ω ^ ρ = ρ from hρE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hXρ
      exact absurd hρv (not_lt.2 this.le)
    refine ⟨?_, hzX'.trans (right_le_opow _ one_lt_omega0), ?_⟩
    · rw [← show ω ^ ρ = ρ from hρE]; exact (opow_le_opow_iff_right one_lt_omega0).2 hρX'
    · exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right X' (opow_pos z' omega0_pos))
  obtain ⟨W3, Z3, w3, m3, b3⟩ := awI_use h hρS hzI
  replace m3 : z' ∈ W3 ∪ Z3 := m3
  -- the witness sets
  have hwz : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (a ≠ 0 → ω ^ X' ∈ W ∪ Z ∧ ω ^ X' + z' ∈ W) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        a ≠ 0 → GxCl (f ρ) (awAt S (f ρ)) (ω ^ a) ∧
          ω ^ gxTh (f ρ) (awAt S (f ρ)) a ≤ f (ω ^ X') := by
    by_cases ha0 : a = 0
    · exact ⟨∅, ∅, WZ.empty, fun h' => absurd ha0 h', fun _ _ _ _ _ h' => absurd ha0 h'⟩
    obtain ⟨W2, Z2, w2, m2, b2⟩ := awI_use h hρS (hwI ha0)
    have ew : gxTh ρ (awAt S ρ) (ω ^ a) = ω ^ X' := gxTh_opow hρS hAt haC
    rw [ew] at m2
    obtain ⟨hρv', hzv', hv'v⟩ := hX'v' ha0
    have hv'δ : ω ^ X' < δ := hv'v.trans hvδ
    have hm3 : z' ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm]
    have hm2 : ω ^ X' ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm]
    have hpos : ω ^ X' < ω ^ X' + z' := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz'0)
    refine ⟨insert (ω ^ X' + z') (W2 ∪ W3), Z2 ∪ Z3,
      (w2.union w3).insW (hρv'.trans le_self_add) (hδI.add_lt hv'δ (hzv.trans hvδ))
        (Or.inr ⟨ω ^ X', hm2, z', hm3, hpos, lt_of_le_of_lt hzv' hpos, rfl⟩),
      fun _ => ⟨by
        rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm], by simp⟩, ?_⟩
    intro A f hW hZ C _
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    obtain ⟨-, c2, p2⟩ := b2 A f hW2 hZ2 C
    obtain ⟨-, -, hσS, -⟩ := aw_σ_facts (S := S) h C
    rw [ew, gxTh_opow hσS (aw_gxAt S _) (aw_opow_code hσS c2)] at p2
    exact ⟨c2, p2⟩
  obtain ⟨W0, Z0, w0, hm0, b0⟩ := hwz
  have hzvz : z' < v + z' := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z' := lt_add_of_pos_right v (pos_iff_ne_zero.2 hz'0)
  have wb : WZ ρ δ (W0 ∪ W3) (insert 0 (Z0 ∪ Z3)) := (w0.union w3).insZ hρE.pos
  have wb2 := wb.union (aw_wz0 h hρS)
  refine ⟨_, _, (wb2.insW hρv.le hvδ (Or.inl (indec_opow _))).insW (hρv.le.trans le_self_add) hvz
      (Or.inr ⟨v, by simp, z', by
        rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm], hvvz, hzvz, rfl⟩),
    by rw [ev]; simp, fun A f hW hZ C => ?_⟩
  -- the copy
  have hsub : ∀ x, x ∈ W0 ∨ x ∈ W3 → x ∈ (A : Set Ordinal.{0}) := fun x hx => hW (by
    rcases hx with hx | hx <;> simp [hx])
  have hsubZ : ∀ x, x ∈ Z0 ∨ x ∈ Z3 ∨ x = 0 → x ∈ A := fun x hx => hZ (by
    rcases hx with hx | hx | hx <;> simp [hx])
  have hW0 : ↑W0 ⊆ A := fun x hx => hsub x (Or.inl (Finset.mem_coe.1 hx))
  have hW3 : ↑W3 ⊆ A := fun x hx => hsub x (Or.inr (Finset.mem_coe.1 hx))
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hsubZ x (Or.inl (Finset.mem_coe.1 hx))
  have hZ3 : ↑Z3 ⊆ A := fun x hx => hsubZ x (Or.inr (Or.inl (Finset.mem_coe.1 hx)))
  have h0A : (0 : Ordinal.{0}) ∈ A := hsubZ 0 (Or.inr (Or.inr rfl))
  have hxA : awNx ρ ∈ A := hW (by simp)
  have hτA : τ ∈ A := hW (by simp)
  have hvA : v ∈ A := hW (by simp)
  have hvzA : v + z' ∈ A := hW (by simp)
  obtain ⟨hzA, czσ, pz⟩ := b3 A f hW3 hZ3 C
  obtain ⟨hfρ, hσ1, hσS, hfE⟩ := aw_σ_facts (S := S) h C
  have hAtσ : GxAt (awAt S (f ρ)) := aw_gxAt S _
  have caσ : GxCl (f ρ) (awAt S (f ρ)) a := by
    by_cases ha0 : a = 0
    · rw [ha0]; exact GxCl.zero hσS.1
    · exact aw_opow_code hσS (b0 A f hW0 hZ0 C ha0).1
  have hcσ : GxCl (f ρ) (awAt S (f ρ)) (ω ^ (a + ω ^ z)) := (GxCl.add caσ (czσ.opow hσS.1)).opow hσS.1
  refine ⟨hcσ, ?_⟩
  rw [ev]
  by_cases hU : UpsPt (f v)
  · exact (aw_ups_big h hρS C hxA hτA hvA hxv hU hcσ).le
  have e1 : gxTh (f ρ) (awAt S (f ρ)) (ω ^ (a + ω ^ z)) =
      ω ^ (gxTh (f ρ) (awAt S (f ρ)) a + ω ^ gxTh (f ρ) (awAt S (f ρ)) z) := by
    rw [gxTh_opow hσS hAtσ (GxCl.add caσ (czσ.opow hσS.1)), gxTh_add hσS hAtσ caσ, gxTh_opow hσS hAtσ czσ]
  rw [e1]
  obtain ⟨a0, ha0, hfa, hdiv⟩ := Gn.gn_src_img h C hsrc hvA hzA hvzA hzv.le hz'0 h0A hU
  rw [hfa]
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  have hπz : ω ^ gxTh (f ρ) (awAt S (f ρ)) z ≤ ω ^ f z' := (opow_le_opow_iff_right one_lt_omega0).2 pz
  by_cases haz : a = 0
  · rw [haz, gxTh_zero, zero_add]
    exact hπz.trans (Ordinal.le_of_dvd ha0 hdiv)
  obtain ⟨hm2, hm2'⟩ := hm0 haz
  obtain ⟨hρv', hzv', hv'v⟩ := hX'v' haz
  have hv'A : ω ^ X' ∈ A := mem_A hm2 hW0 hZ0
  have hv'zA : ω ^ X' + z' ∈ A := hW0 (Finset.mem_coe.2 hm2')
  obtain ⟨-, p2⟩ := b0 A f hW0 hZ0 C haz
  obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hv'A (indec_opow _))
  have hbc : gxTh (f ρ) (awAt S (f ρ)) a ≤ c := by
    rw [hc] at p2; exact (opow_le_opow_iff_right one_lt_omega0).1 p2
  have hca : c < a0 := by
    have := C.mono hv'A hvA hv'v
    rw [hc, hfa] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : f ρ ≤ f (ω ^ X') := (C.mono.le_iff_le C.rho hv'A).2 hρv'
    rw [hc, h0, opow_zero] at h1
    exact absurd (one_lt_omega0.trans (omega0_lt_inE hfE)) (not_lt.2 h1)
  have hX'n := hX'0 haz
  have hcdiv : ω ^ f z' ∣ c ∨ (InE c ∧ c < ω ^ f z') := by
    by_cases hU' : UpsPt (f (ω ^ X'))
    · have hcE : InE c := by
        have := upsPt_inE hU'
        rw [hc] at this
        exact (inE_opow_iff c).1 this
      rcases le_or_gt (f z') c with hzc | hcz
      · exact Or.inl (opow_dvd_of_inE hcE hzc)
      · exact Or.inr ⟨hcE, by
          rw [← show ω ^ c = c from hcE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hcz⟩
    · have hρv'' : ρ < ω ^ X' := by
        rcases hρv'.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso; rw [← heq] at hU'; exact hU' C.ups
      have hsrc' : le1 (ω ^ X') (ω ^ X' + z') :=
        Gn.gn_src h hX'n hz'0 hd' hzv' hρv'' (hδI.add_lt (hv'v.trans hvδ) (hzv.trans hvδ)).le
      obtain ⟨c', -, hfc', hdc'⟩ := Gn.gn_src_img h C hsrc' hv'A hzA hv'zA hzv' hz'0 h0A hU'
      have hcc : c' = c := opow_inj (hfc'.symm.trans hc)
      exact Or.inl (hcc ▸ hdc')
  rcases hcdiv with hcd | ⟨hcE, hcz⟩
  · calc gxTh (f ρ) (awAt S (f ρ)) a + ω ^ gxTh (f ρ) (awAt S (f ρ)) z ≤ c + ω ^ f z' := add_le_add hbc hπz
      _ ≤ a0 := dvd_next hdiv hcd hca
  · calc gxTh (f ρ) (awAt S (f ρ)) a + ω ^ gxTh (f ρ) (awAt S (f ρ)) z ≤ c + ω ^ f z' := add_le_add hbc hπz
      _ = ω ^ f z' := add_of_omega0_opow_le (by rw [← show ω ^ c = c from hcE] at hcz ⊢; exact hcz) le_rfl
      _ ≤ a0 := Ordinal.le_of_dvd ha0 hdiv

/-- Witness sets for finitely many codes with Lemma IMG. -/
theorem awI_fin : ∀ s : Finset Ordinal.{0}, (∀ c ∈ s, AwI S ρ δ c) →
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A →
      ↑Z ⊆ A → ImgCtx ρ A f → ∀ c ∈ s, gxTh ρ (awAt S ρ) c ∈ A ∧ GxCl (f ρ) (awAt S (f ρ)) c ∧
        gxTh (f ρ) (awAt S (f ρ)) c ≤ f (gxTh ρ (awAt S ρ) c) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨∅, ∅, WZ.empty, fun _ _ _ _ _ x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a s _ IH =>
    intro hs
    obtain ⟨W, Z, w, b⟩ := IH fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨Wa, Za, wa, -, ba⟩ := awI_use h hρS (hs a (Finset.mem_insert_self a s))
    refine ⟨W ∪ Wa, Z ∪ Za, w.union wa, fun A f hW hZ C x hx => ?_⟩
    have hW1 : ↑W ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hZ1 : ↑Z ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hy)))
    have hW2 : ↑Wa ⊆ A := fun y hy => hW (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    have hZ2 : ↑Za ⊆ A := fun y hy => hZ (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hy)))
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ba A f hW2 hZ2 C
    · exact b A f hW1 hZ1 C x hx

end Img

/-- **The base of minimality** at a `υ`-point `x`: the greatest `<₁`-predecessor `τ'` of `e` in `[x, e)` (or `x`). -/
theorem aw_base {x e : Ordinal.{0}} (hxU : UpsPt x) (hx1 : x < Om1) (heT : e ∈ Tset x) (hρe : x < e) (he1 : e < Om1)
    (heI : Indec e) :
    ∃ τ', x ≤ τ' ∧ τ' < e ∧ InE τ' ∧ le1R τ' e ∧ e ∈ Tset τ' ∧ ∀ d, le1R d e → d < e → d ≤ τ' := by
  have hρE : InE x := upsPt_inE hxU
  obtain ⟨mρ, hρm, hmL, hmmin, hTm⟩ := T_inter_Om1 hρE hx1
  have hem : e < mρ := (hTm e he1).1 heT
  obtain ⟨n, β, hβn, hρβ0, hmin0, hch⟩ := le1R_loc (Or.inr hρE) hx1 heT hρe he1 heI
  have hβρ : ∀ i ≤ n, x < β i := by
    intro i
    induction i with
    | zero => exact fun _ => hρβ0
    | succ k ih => exact fun hk => (ih (Nat.le_of_succ_le hk)).trans (hch k (Nat.lt_of_succ_le hk)).1
  cases n with
  | zero =>
    rw [← hβn]
    refine ⟨x, le_rfl, hρβ0, hρE, hxU.2 _ hρβ0.le, ?_, hmin0⟩
    rw [hβn]; exact heT
  | succ k =>
    obtain ⟨hlt, hR, hmin⟩ := hch k (Nat.lt_succ_self k)
    rw [hβn] at hlt hR hmin
    have hρk : x < β k := hβρ k (Nat.le_succ k)
    have hk0 : 0 < β k := lt_of_le_of_lt zero_le hρk
    have hkk : β k * 2 ≤ e := by rw [mul_two_eq]; exact (heI.add_lt hlt hlt).le
    have hkE : InE (β k) := (le1R_two_iff hk0).1
      (le1R_of_le (by rw [mul_two_eq]; exact le_self_add) hkk hR)
    have hk1 : β k < Om1 := hlt.trans he1
    obtain ⟨m', hkm', hm'L, hm'min, hTm'⟩ := T_inter_Om1 hkE hk1
    have hem' : e < m' := by
      by_contra hle
      push Not at hle
      have := hmmin m' (hρk.trans hkm') hm'L
      exact absurd (hem.trans_le (this.trans hle)) (lt_irrefl _)
    exact ⟨β k, hρk.le, hlt, hkE, hR, (hTm' e he1).2 hem', hmin⟩

section Eps

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hρS : SC ρ)
include h hρS

/-- **LEMMA IMG AT AN `ε`-CODE ABOVE `θ`**, given it below ([W07b] Claim 5.6 at the base `τ' ≥ x`, the FRAG map from `(σ, x')` to
`(ρ, x)`). -/
theorem awE_core {c : Ordinal.{0}} (heE : InE (gxTh ρ (awAt S ρ) c)) (hθc : awNx ρ < gxTh ρ (awAt S ρ) c) (hcV : c ≤ awV S)
    (P : Finset Ordinal.{0}) (hP : ∀ p ∈ P, p < ρ)
    (hLt : ∀ y, SC y → y < Om1 → (∀ p ∈ P, p < y) → gxTh y (awAt S y) c < awNx (awNx y))
    (IH : ∀ c₀, GxCl ρ (awAt S ρ) c₀ → c₀ < c → AwI S ρ δ c₀) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gxTh ρ (awAt S ρ) c ∈ W ∪ Z ∧ P ⊆ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        gxTh (f ρ) (awAt S (f ρ)) c ≤ f (gxTh ρ (awAt S ρ) c) := by
  classical
  have hρ1 := h.ρ1
  have hρE := h.ρE
  obtain ⟨hρx, hxτ, hxU, hmτ⟩ := aw_x_facts h hρS
  obtain ⟨-, -, hxS, hx1, -, -⟩ := awNx_facts hρS hρ1
  obtain ⟨hxm, hmU, hmS, hm1, hTm, hnx⟩ := awNx_facts hxS hx1
  set x := awNx ρ with hxdef
  set m := awNx x with hmdef
  set e := gxTh ρ (awAt S ρ) c with hedef
  have hxe : x < e := hθc
  have hem : e < m := hLt ρ hρS hρ1 hP
  have he1 : e < Om1 := hem.trans hm1
  have heT : e ∈ Tset x := (hTm e he1).2 hem
  have heI : Indec e := inE_indec heE
  obtain ⟨τ', hxτ', hτ'e, hτ'E, -, heT', hmin⟩ := aw_base hxU hx1 heT hxe he1 heI
  obtain ⟨l, hl, X, Z, hX, hZ, heZ, hlZ, hno⟩ :=
    claim56pw (Or.inr hτ'E) (hτ'e.trans he1) heT' hτ'e he1 heI hmin
  have hel : e ≤ l := le1R_le hl.1
  have heU : ¬ UpsPt e := fun hU => absurd (hnx.2.2 e hxe hU) (not_le.2 hem)
  have hlm : l < m := by
    by_contra hle
    push Not at hle
    exact heU ⟨lt_of_le_of_lt zero_le hxe, (le1R_lt_ups hmU hem hle).1 hl.1⟩
  have hlδ : l < δ := hlm.trans (hmτ.trans h.τδ)
  have hδI := inE_indec h.δE
  -- the closed hull of `X ∪ Z ∪ {τ'}`, with the sums of two of its members
  set S0 : Finset Ordinal.{0} := insert τ' (X ∪ Z) with hS0
  obtain ⟨Cs, hSC, hCcl, hCb⟩ := exists_closed S0
  have hS0l : ∀ s ∈ S0, s ≤ l := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact (hτ'e.trans_le hel).le
    rcases Finset.mem_union.1 hs with hs | hs
    · exact ((hX s hs).trans_le hel).le
    · exact (hZ s hs).2
  have hCl : ∀ c ∈ Cs, c ≤ l := fun c hc => by
    obtain ⟨s, hs, hcs⟩ := hCb c hc
    exact hcs.trans (hS0l s hs)
  set D : Finset Ordinal.{0} := Cs ∪ Finset.image₂ (· + ·) Cs Cs with hD
  have hDδ : ∀ d ∈ D, d < δ := by
    intro d hd
    rcases Finset.mem_union.1 hd with hd | hd
    · exact (hCl d hd).trans_lt hlδ
    · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.1 hd
      exact hδI.add_lt ((hCl a ha).trans_lt hlδ) ((hCl b hb).trans_lt hlδ)
  set W1 := D.filter (fun d => ρ ≤ d) with hW1
  set Z1 := D.filter (fun d => d < ρ) with hZ1
  have hDWZ : ∀ d ∈ D, d ∈ W1 ∪ Z1 := fun d hd => by
    rcases le_or_gt ρ d with hρd | hdρ
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hd, hρd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hd, hdρ⟩)
  have hCD : ∀ c ∈ Cs, c ∈ D := fun c hc => Finset.mem_union_left _ hc
  have w1 : WZ ρ δ W1 Z1 := by
    refine ⟨fun w hw => ⟨(Finset.mem_filter.1 hw).2, hDδ w (Finset.mem_filter.1 hw).1⟩,
      fun z hz => (Finset.mem_filter.1 hz).2, fun w hw => ?_⟩
    obtain ⟨hwD, hρw⟩ := Finset.mem_filter.1 hw
    have hw0 : w ≠ 0 := (lt_of_lt_of_le hρE.pos hρw).ne'
    by_cases hwC : w ∈ Cs
    · by_cases hdec : DecompR0 w
      · rcases hCcl w hwC hdec with h0 | ⟨y, hy, z, hz, hyw, hzw, hyz⟩
        · exact absurd h0 hw0
        · exact Or.inr ⟨y, hDWZ y (hCD y hy), z, hDWZ z (hCD z hz), hyw, hzw, hyz⟩
      · exact Or.inl hdec
    · rcases Finset.mem_union.1 hwD with hwC' | hw2
      · exact absurd hwC' hwC
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_image₂.1 hw2
      have hb0 : b ≠ 0 := fun h0 => hwC (by rw [← hab, h0, add_zero]; exact ha)
      have hbw : b ≠ w := fun e => hwC (e ▸ hb)
      refine Or.inr ⟨a, hDWZ a (hCD a ha), b, hDWZ b (hCD b hb), ?_, ?_, hab⟩
      · rw [← hab]; exact lt_add_of_pos_right a (pos_iff_ne_zero.2 hb0)
      · exact lt_of_le_of_ne (le_add_self.trans_eq hab) hbw
  -- the codes of the points of `insert τ' X`
  have hcod : ∀ y₀, y₀ ∈ insert τ' X → ∃ c₀, GxCl ρ (awAt S ρ) c₀ ∧ c₀ < c ∧ gxTh ρ (awAt S ρ) c₀ = y₀ := by
    intro y₀ hy₀
    have hy₀e : y₀ < gxTh ρ (awAt S ρ) c := by
      rcases Finset.mem_insert.1 hy₀ with rfl | hy₀
      · exact hτ'e
      · exact hX y₀ hy₀
    exact gxTh_onto hy₀e
  choose! cd hcd1 hcd2 hcd3 using hcod
  set C₀ : Finset Ordinal.{0} := (insert τ' X).image cd with hC₀
  have hC₀l : ∀ c₀ ∈ C₀, GxCl ρ (awAt S ρ) c₀ ∧ c₀ < c := by
    intro c₀ hc₀
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hc₀
    exact ⟨hcd1 y₀ hy₀, hcd2 y₀ hy₀⟩
  obtain ⟨W2, Z2, w2, b2⟩ := awI_fin h hρS C₀ fun c₀ hc₀ => IH c₀ (hC₀l c₀ hc₀).1 (hC₀l c₀ hc₀).2
  have heS : e ∈ S0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ heZ)
  have hlS : l ∈ S0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ hlZ)
  have heW1 : e ∈ W1 := Finset.mem_filter.2 ⟨hCD e (hSC heS), (hρx.trans hxe).le⟩
  have wall := ((w1.union w2).union (aw_wz0 h hρS)).union (Gj.wz_consts (δ := δ) (C := P) hP)
  refine ⟨_, _, wall, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ heW1))), Finset.subset_union_right, fun A f hWg hZg Cx => ?_⟩
  have hWA : ∀ d, d ∈ W1 ∨ d ∈ W2 ∨ d ∈ ({x, τ} : Finset Ordinal.{0}) → d ∈ A := fun d hd =>
    hWg (Finset.mem_coe.2 (Finset.mem_union_left _ (by
      rcases hd with hd | hd | hd
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hd)
      · exact Finset.mem_union_right _ hd)))
  have hZA : ∀ d, d ∈ Z1 ∨ d ∈ Z2 ∨ d ∈ P → d ∈ A := fun d hd => hZg (by
    rcases hd with hd | hd | hd <;> simp [hd])
  have hDA : ∀ d ∈ D, d ∈ A := fun d hd => by
    rcases Finset.mem_union.1 (hDWZ d hd) with h1 | h1
    · exact hWA d (Or.inl h1)
    · exact hZA d (Or.inl h1)
  have hSA : ∀ s ∈ S0, s ∈ A := fun s hs => hDA s (hCD s (hSC hs))
  have hW2A : ↑W2 ⊆ A := fun y hy => hWA y (Or.inr (Or.inl (Finset.mem_coe.1 hy)))
  have hZ2A : ↑Z2 ⊆ A := fun y hy => hZA y (Or.inr (Or.inl (Finset.mem_coe.1 hy)))
  have hIMG := b2 A f hW2A hZ2A Cx
  have hxA : x ∈ A := hWA x (Or.inr (Or.inr (by simp)))
  have hτA : τ ∈ A := hWA τ (Or.inr (Or.inr (by simp)))
  have heA : e ∈ A := hSA e heS
  have hlA : l ∈ A := hSA l hlS
  obtain ⟨hfρ, hσ1, hσS, hσE⟩ := aw_σ_facts (S := S) h Cx
  by_contra hlt
  push Not at hlt
  set σ := f ρ with hσdef
  obtain ⟨hσx', hx'U, hx'S, hx'1, -, hx'n⟩ := awNx_facts hσS hσ1
  obtain ⟨hx'm, hm'U, -, hm'1, -, hm'n⟩ := awNx_facts hx'S hx'1
  set x' := awNx σ with hx'def
  set m' := awNx x' with hm'def
  have he'm : gxTh σ (awAt S σ) c < m' :=
    hLt σ hσS hσ1 fun p hp => Cx.above p (hZA p (Or.inr (Or.inr hp))) (hP p hp)
  obtain ⟨c₁, hc₁σ, hc₁c, hc₁e⟩ := gxTh_onto hlt
  have hfem : f e < m' := hlt.trans he'm
  have hfxe : f x < f e := Cx.mono hxA heA hxe
  have hfxU := aw_fx_ups h hρS Cx hxA hτA
  have hfx : f x = x' := by
    have h1 : x' ≤ f x := aw_fx h hρS S Cx hxA hτA
    rcases h1.lt_or_eq with h2 | h2
    · exact absurd ((hm'n.2.2 _ h2 hfxU).trans_lt (hfxe.trans hfem)) (lt_irrefl _)
    · exact h2.symm
  have hfeU : ¬ UpsPt (f e) := fun hU => by
    have h1 : x' < f e := (hfx.symm.le).trans_lt hfxe
    exact absurd ((hm'n.2.2 _ h1 hU).trans_lt hfem) (lt_irrefl _)
  have hle1R : ∀ a b, a ∈ A → b ∈ A → ρ < a → b ≤ δ → le1R a b → le1R (f a) (f b) := by
    intro a b haA hbA hρa hbδ hab
    have hf1 := Cx.cov1 a haA b hbA ((h.lowδ a b hρa hbδ).2 hab)
    by_cases hU : UpsPt (f a)
    · exact hU.2 _ (Cx.mono.monotoneOn haA hbA (le1R_le hab))
    · exact (Cx.sk (f a) (Cx.low a haA) hU (f b)).1 hf1
  have hρe : ρ < e := hρx.trans hxe
  have hfl : f l < m' := by
    by_contra hge
    push Not at hge
    exact hfeU ⟨lt_of_le_of_lt zero_le hfxe, (le1R_lt_ups hm'U hfem hge).1 (hle1R e l heA hlA hρe hlδ.le hl.1)⟩
  have hfb : ∀ y ∈ S0, f y < m' := fun y hy =>
    (Cx.mono.monotoneOn (hSA y hy) hlA (hS0l y hy)).trans_lt hfl
  -- the codes moved
  have hs₀ : ∀ c₀ ∈ insert c₁ C₀, GxCl σ (awAt S σ) c₀ ∧ c₀ < awV S := by
    intro c₀ hc₀
    rcases Finset.mem_insert.1 hc₀ with rfl | hc₀
    · exact ⟨hc₁σ, hc₁c.trans_le hcV⟩
    · exact ⟨(hIMG c₀ hc₀).2.1, (hC₀l c₀ hc₀).2.trans_le hcV⟩
  obtain ⟨H, hs₀H, hH⟩ := aw_closure_fin hσS hσ1 _ hs₀
  have hRdH : ∀ z ∈ H, gxTh σ (awAt S σ) z < m' := fun z hz => aw_Rd_lt hσS hσ1 (hH z hz).1.1
  -- the domain of the FRAG map
  set Bs : Finset Ordinal.{0} := S0.image f ∪ ({σ, x'} : Finset Ordinal.{0}) ∪
    H.image (fun z => gxTh σ (awAt S σ) z) ∪ H.image (fun z => cdOff (gxTh σ (awAt S σ) z)) with hBs
  have hBslt : ∀ w ∈ Bs, w < m' := by
    intro w hw
    simp only [hBs, Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with ((⟨y, hy, rfl⟩ | rfl | rfl) | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩
    · exact hfb y hy
    · exact hσx'.trans hx'm
    · exact hx'm
    · exact hRdH z hz
    · exact (cdOff_le _).trans_lt (hRdH z hz)
  set F := Bs.biUnion (hpar σ) with hF
  have hBF : ∀ w ∈ Bs, w ∈ F := fun w hw => Finset.mem_biUnion.2 ⟨w, hw, mem_hpar_self _ _⟩
  have hFlt : ∀ w ∈ F, w < m' := by
    intro w hw
    obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.1 hw
    exact (hpar_le _ u w hwu).trans_lt (hBslt u hu)
  have hFcl : ∀ z ∈ F, σ ≤ z → ∀ p ∈ Par (sb z) z, p < z → p ∈ F := by
    intro z hz hρz p hp hpz
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hz
    exact Finset.mem_biUnion.2 ⟨w, hw, hpar_closed _ w z hzw hρz p hp hpz⟩
  have hfF : ∀ y ∈ S0, f y ∈ F := fun y hy => hBF _ (by
    simp only [hBs, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl ⟨y, hy, rfl⟩)))
  have hσF : σ ∈ F := hBF _ (by simp [hBs])
  have hx'F : x' ∈ F := hBF _ (by simp [hBs])
  have hRF : ∀ z ∈ H, gxTh σ (awAt S σ) z ∈ F := fun z hz => hBF _ (by
    simp only [hBs, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨z, hz, rfl⟩))
  have hOF : ∀ z ∈ H, cdOff (gxTh σ (awAt S σ) z) ∈ F := fun z hz => hBF _ (by
    simp only [hBs, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨z, hz, rfl⟩)
  -- the base `κ`, an `ε`-number below `σ`
  set P : Finset Ordinal.{0} := (H.biUnion fun z => insert z (wP z)) ∪ F with hP
  have hsup : (insert 0 (P.filter (· < σ))).sup id < σ := by
    rw [Finset.sup_lt_iff hσE.pos]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hσE.pos
    · exact (Finset.mem_filter.1 hb).2
  set κ := eN ((insert 0 (P.filter (· < σ))).sup id) with hκdef
  have hκE : InE κ := eN_E _
  have hκσ : κ < σ := Go.go_eN_lt_SC hσS hsup
  have hκρ : κ < ρ := hκσ.trans hfρ
  have hLo : ∀ w ∈ P, w < σ → w < κ := fun w hw hwσ =>
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem
      (show w ∈ P.filter (· < σ) from Finset.mem_filter.2 ⟨hw, hwσ⟩))) (lt_eN _)
  have hFκ : ∀ w ∈ F, w < σ → w < κ := fun w hw => hLo w (Finset.mem_union_right _ hw)
  have hW : ∀ z ∈ H, z < ConjT.th S → WDom S κ z := by
    intro z hz hzθ
    rcases (xi_dom_codes hσS hσ1 hzθ).1 ((aw_code_th hzθ).1 (hH z hz).1.1) with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl (hLo z (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_insert_self _ _⟩)) h1)
    · exact Or.inr ⟨h1, h2, fun p hp => hLo p (Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨z, hz, Finset.mem_insert_of_mem hp⟩)) (h3 p hp)⟩
  -- the chains
  set b : ℕ → Ordinal.{0} := fun j => if j = 0 then σ else x' with hbdef
  set c' : ℕ → Ordinal.{0} := fun j => if j = 0 then ρ else x with hc'def
  have hκ1 : κ < Om1 := hκσ.trans hσ1
  have hbU : ∀ k, k < 2 → UpsPt (b k) ∧ b k < Om1 := by
    intro k _
    by_cases hk : k = 0
    · simp only [hbdef, if_pos hk]; exact ⟨Cx.ups, hσ1⟩
    · simp only [hbdef, if_neg hk]; exact ⟨hx'U, hx'1⟩
  have hbC : Chain κ b 2 := by
    refine ⟨hκE, hκ1, hbU, fun j k hjk hk => ?_, fun k _ => ?_⟩
    · obtain rfl : j = 0 := by omega
      obtain rfl : k = 1 := by omega
      simpa [hbdef] using hσx'
    · by_cases hk : k = 0
      · simp only [hbdef, if_pos hk]; exact hκσ
      · simp only [hbdef, if_neg hk]; exact hκσ.trans hσx'
  have hcC : Chain κ c' 2 := by
    refine ⟨hκE, hκ1, fun k _ => ?_, fun j k hjk hk => ?_, fun k _ => ?_⟩
    · by_cases hk : k = 0
      · simp only [hc'def, if_pos hk]; exact ⟨h.ρU, hρ1⟩
      · simp only [hc'def, if_neg hk]; exact ⟨hxU, hx1⟩
    · obtain rfl : j = 0 := by omega
      obtain rfl : k = 1 := by omega
      simpa [hc'def] using hρx
    · by_cases hk : k = 0
      · simp only [hc'def, if_pos hk]; exact hκρ
      · simp only [hc'def, if_neg hk]; exact hκρ.trans hρx
  have hseg : ∀ z ∈ F, σ ≤ z → ∃ j < 2, InSeg (b j) z := by
    intro z hz hσz
    have hzm := hFlt z hz
    rcases lt_or_ge z x' with hzx | hxz
    · refine ⟨0, by omega, ?_⟩
      simp only [hbdef, if_true]
      exact ⟨hσz, hzx.trans hx'1, fun u hu hU => hzx.trans_le (hx'n.2.2 u hu hU)⟩
    · refine ⟨1, by omega, ?_⟩
      simp only [hbdef, one_ne_zero, if_false]
      exact ⟨hxz, hzm.trans hm'1, fun u hu hU => hzm.trans_le (hm'n.2.2 u hu hU)⟩
  have hFDD : (↑F : Set Ordinal.{0}) ⊆ DD κ b 2 := by
    suffices H' : ∀ z, z ∈ F → z ∈ DD κ b 2 from fun z hz => H' z hz
    intro z
    induction z using WellFoundedLT.induction with
    | ind z IH' =>
    intro hz
    rcases lt_or_ge z σ with hzσ | hσz
    · exact Iio_sub_DD _ (hFκ z hz hzσ)
    obtain ⟨j, hj, hs⟩ := hseg z hz hσz
    have hU := hbU j hj
    have hzT : z ∈ Tset (b j) := ((inSeg_iff hU.1 hU.2).1 hs).2.2
    have hsb : sb z = b j := sb_eq hU.1 hs
    have hPar : ↑(Par (b j) z) ⊆ ClS (DD κ b j) := by
      intro p hp
      have hpb : p < b j := Par_sub (upsPt_inE hU.1) hU.2 hzT hp
      have hpz : p < z := lt_of_lt_of_le hpb hs.1
      have hpF : p ∈ F := hFcl z hz hσz p (by rw [hsb]; exact Finset.mem_coe.1 hp) hpz
      exact ClS.sub _ (DD_down hbC (IH' p hpz hpF) hj hpb)
    exact DD_mono (show j + 1 ≤ 2 by omega) (Or.inr ⟨hs, hzT, hPar⟩)
  -- FRAG, and the readings moved
  obtain ⟨Ψ, hΨ⟩ := Xj.xjFragXe hbC hcC F hFDD
  obtain ⟨⟨⟨⟨Q1, -, Q3, Q4, Q5, -, -⟩, -⟩, -⟩, -⟩ := hΨ.1.1
  have hΨρ : Ψ σ = ρ := by
    have := Q3 0 (by omega) (by simpa [hbdef] using hσF)
    simpa [hbdef, hc'def] using this
  have hCAN : ∀ z ∈ H, Ψ (gxTh σ (awAt S σ) z) = gxTh ρ (awAt S ρ) z := by
    refine aw_can hσS hσ1 hρS hρ1 hκE hκσ hκρ le_rfl (by simp [hbdef])
      (by simp only [hbdef, one_ne_zero, if_false]; exact hx'def) (by simp [hc'def])
      (by simp only [hc'def, one_ne_zero, if_false]; exact hxdef) hΨ ?_ hW hRF hOF hx'F
    exact fun z hz => ⟨(hH z hz).1.1, (hH z hz).1.1.mono hfρ.le ((awU S).mono _ _ hfρ.le), (hH z hz).1.2, (hH z hz).2⟩
  have hcH : c₁ ∈ H := hs₀H (Finset.mem_insert_self _ _)
  have hheh : Ψ (f e) < e := by
    have h1 := hCAN c₁ hcH
    rw [hc₁e] at h1
    rw [h1]
    exact gxTh_lt (hc₁σ.mono hfρ.le ((awU S).mono _ _ hfρ.le)) hc₁c
  -- the covering
  have hlow : ∀ y ∈ S0, y < ρ → Ψ (f y) = y := by
    intro y hy hyρ
    have hyA := hSA y hy
    have hfy : f y = y := Cx.fix y hyA hyρ
    have hyσ : y < σ := Cx.above y hyA hyρ
    have hyF : y ∈ F := by rw [← hfy]; exact hfF y hy
    rw [hfy]; exact Q1 y hyF (hFκ y hyF hyσ)
  have hmono0 : ∀ a ∈ S0, ∀ b ∈ S0, a < b → Ψ (f a) < Ψ (f b) := fun a ha b hb hab =>
    Q4.2.1 (hfF a ha) (hfF b hb) (Cx.mono (hSA a ha) (hSA b hb) hab)
  have hpw : ∀ y₀ ∈ insert τ' X, y₀ ≤ Ψ (f y₀) := by
    intro y₀ hy₀
    have hcmem : cd y₀ ∈ C₀ := Finset.mem_image_of_mem _ hy₀
    obtain ⟨-, -, hle⟩ := hIMG _ hcmem
    rw [hcd3 y₀ hy₀] at hle
    have hcH' : cd y₀ ∈ H := hs₀H (Finset.mem_insert_of_mem hcmem)
    have hy₀S : y₀ ∈ S0 := by
      rcases Finset.mem_insert.1 hy₀ with rfl | hy₀
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hy₀)
    have h1 := Q4.2.1.monotoneOn (hRF _ hcH') (hfF y₀ hy₀S) hle
    rw [hCAN _ hcH', hcd3 y₀ hy₀] at h1
    exact h1
  have hsub : ∀ a ∈ X ∪ Z, a ∈ S0 := fun a ha => Finset.mem_insert_of_mem ha
  have hcov1 : ∀ a ∈ X ∪ Z, ∀ b ∈ X ∪ Z, le1R a b → le1R (Ψ (f a)) (Ψ (f b)) := by
    intro a ha b hb hab
    have haS := hsub a ha
    have hbS := hsub b hb
    have haA := hSA a haS
    have hbA := hSA b hbS
    rcases (le1R_le hab).lt_or_eq with hab' | rfl
    swap
    · exact le1R_refl _
    have hgab := (hmono0 a haS b hbS hab').le
    rcases lt_or_ge a ρ with haρ | hρa
    · by_cases haU : UpsPt a
      · have e1 := hlow a haS haρ
        rw [e1] at hgab ⊢
        exact haU.2 _ hgab
      · rcases lt_or_ge b ρ with hbρ | hρb
        · rw [hlow a haS haρ, hlow b hbS hbρ]; exact hab
        · exact absurd ((Cx.sk a haρ haU b).2 hab) (h.below a haρ b hρb)
    · rcases hρa.lt_or_eq with hρa' | heq
      · exact (Q5 _ (hfF a haS) _ (hfF b hbS)).1 (hle1R a b haA hbA hρa' ((hS0l b hbS).trans hlδ.le) hab)
      · have hga : Ψ (f a) = ρ := by rw [← heq, ← hσdef]; exact hΨρ
        rw [hga] at hgab ⊢
        exact h.ρU.2 _ hgab
  have hhl : Ψ (f l) < e := by
    by_contra hge
    push Not at hge
    have hR := hcov1 e (Finset.mem_union_right _ heZ) l (Finset.mem_union_right _ hlZ) hl.1
    have h1 := hmin _ (le1R_of_le hheh.le hge hR) hheh
    have h2 := (hpw τ' (Finset.mem_insert_self _ _)).trans_lt
      (hmono0 τ' (Finset.mem_insert_self _ _) e heS hτ'e)
    exact absurd h2 (not_lt.2 h1)
  apply hno
  refine ⟨fun y => Ψ (f y), ⟨fun a ha b hb hab => hmono0 a (hsub a ha) b (hsub b hb) hab, fun a ha b hb c₁ hc₁ => ?_,
    hcov1⟩, fun y hy => hpw y (Finset.mem_insert_of_mem hy), fun y hy z hz => ?_, fun z hz => ?_⟩
  · -- `+`, both directions
    have haS := hsub a ha
    have hbS := hsub b hb
    have hcS := hsub c₁ hc₁
    have habD : a + b ∈ D := Finset.mem_union_right _ (Finset.mem_image₂.2 ⟨a, hSC haS, b, hSC hbS, rfl⟩)
    have habA : a + b ∈ A := hDA _ habD
    have hfab : f a + f b = f (a + b) := Cx.add a (hSA a haS) b (hSA b hbS) (a + b) habA rfl
    constructor
    · rintro rfl
      exact (Q4.2.2 _ (hfF a haS) _ (hfF b hbS) _ (hfF _ hcS)).1 hfab
    · intro hg
      have e1 := (Q4.2.2 _ (hfF a haS) _ (hfF b hbS) _ (hfF _ hcS)).2 hg
      exact Cx.mono.injOn habA (hSA c₁ hcS) (hfab.symm.trans e1)
  · -- `h[X] < h[Z]`
    exact hmono0 y (hsub y (Finset.mem_union_left _ hy)) z (hsub z (Finset.mem_union_right _ hz))
      ((hX y hy).trans_le (hZ z hz).1)
  · -- `h[Z] < e`
    have hzS := hsub z (Finset.mem_union_right _ hz)
    rcases (hZ z hz).2.lt_or_eq with hzl | rfl
    · exact (hmono0 z hzS l hlS hzl).trans hhl
    · exact hhl

/-- **LEMMA IMG AT AN `ε`-CODE ABOVE `θ`**, given it below. -/
theorem awI_eps {c : Ordinal.{0}} (hc : GxCl ρ (awAt S ρ) c) (hE : ω ^ c = c) (hθc : ConjT.th S < c) (hcV : c < awV S)
    (IH : ∀ c₀, GxCl ρ (awAt S ρ) c₀ → c₀ < c → AwI S ρ δ c₀) : AwI S ρ δ c := by
  classical
  have hxe : awNx ρ < gxTh ρ (awAt S ρ) c := by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.atom (aw_th_mem _)) hθc
    rwa [aw_Rd_th hρS h.ρ1] at this
  obtain ⟨Z', hZ', hc'⟩ := (awU S).support hρS hc
  have hcode : ∀ y, Z' ≤ y → GxCl y (awAt S y) c := fun y hy => hc'.mono hy ((awU S).mono _ _ hy)
  obtain ⟨W, Z, w, m, hP, b⟩ := awE_core h hρS ((aw_Rd_E_iff hρS hc).1 hE) hxe hcV.le {Z'} (by simpa using hZ')
    (fun y hy hy1 hp => aw_Rd_lt hy hy1 (hcode y (hp Z' (by simp)).le)) IH
  refine ⟨W, Z, w, m, fun A f hW hZ C => ⟨?_, b A f hW hZ C⟩⟩
  have hZA : Z' ∈ A := hZ (Finset.mem_coe.2 (hP (by simp)))
  exact hcode _ (C.above Z' hZA hZ').le

/-- **LEMMA IMG AT EVERY CODE BELOW `K_ω`.** -/
theorem aw_img : ∀ c, GxCl ρ (awAt S ρ) c → c < awV S → AwI S ρ δ c := by
  have hAt : GxAt (awAt S ρ) := aw_gxAt S ρ
  obtain ⟨hρx, hxτ, hxU, -⟩ := aw_x_facts h hρS
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcV
  have IH' : ∀ d, GxCl ρ (awAt S ρ) d → d < c → AwI S ρ δ d := fun d hd hdc => IH d hdc hd (hdc.trans hcV)
  rcases lt_trichotomy c (ConjT.th S) with hcθ | rfl | hθc
  · exact awI_low h hρS hcθ hc
  · exact awI_th h hρS
  have hxv : awNx ρ < gxTh ρ (awAt S ρ) c := by
    have := gxTh_lt (Z := ρ) (At := awAt S ρ) (GxCl.atom (aw_th_mem _)) hθc
    rwa [aw_Rd_th hρS h.ρ1] at this
  have hρv : ρ ≤ gxTh ρ (awAt S ρ) c := (hρx.trans hxv).le
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hθc).ne'
  by_cases hI : Indec c
  · by_cases hE : ω ^ c = c
    · exact awI_eps h hρS hc hE hθc hcV IH'
    obtain ⟨a, rfl⟩ := indec_eq_opow hI
    have hac : GxCl ρ (awAt S ρ) a := aw_opow_code hρS hc
    have hac' : a < ω ^ a := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hE (by rw [← e, ← e]))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [opow_zero] at hθc
      exact absurd (one_lt_omega0.trans (omega0_lt_inE aw_th_E)) (not_lt.2 hθc.le)
    obtain ⟨a', z, ha'c, hzc, e, hd, ha'a, hza⟩ := aw_lg_parts hρS a ha0 hac
    have hwa : ω ^ a' < ω ^ a := (opow_lt_opow_iff_right one_lt_omega0).2 ha'a
    have hwI : AwI S ρ δ (ω ^ a') := IH' _ (ha'c.opow hρS.1) hwa
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [opow_zero] at e
      rw [e] at hc hcV hρv hθc hE hac' IH IH' hxv ⊢
      exact awI_succ h hρS ha'c hwI hρv
    · rw [e] at hc hcV hρv hθc hE hac' IH IH' hxv hza ⊢
      exact awI_lim h hρS ha'c hzc hz0 hd (IH' z hzc (hza.trans_lt hac')) (fun _ => hwI) hac' hθc
  · -- a sum
    have hl := lead_add_tail hc0
    have hlc : lead c ≤ c := lead_le hc0
    have hlt : lead c < c := lt_of_le_of_ne hlc (fun e => hI (e ▸ indec_opow _))
    have htc : tail c < c := tail_lt hc0
    have hlcode : GxCl ρ (awAt S ρ) (lead c) := (gxDec hρS hAt c hc).2.opow hρS.1
    have htcode : GxCl ρ (awAt S ρ) (tail c) := (gxDec hρS hAt c hc).1 _ hlcode hlc
    have := awI_add h hρS hlcode htcode (IH' _ hlcode hlt) (IH' _ htcode htc) (by rw [hl]; exact hlt) (by rw [hl]; exact htc)
      (by rw [hl]; exact hρv)
    rwa [hl] at this

/-- **THE IMG PACKAGE AT A CODE BELOW `K_ω`.** -/
theorem aw_pkg {c : Ordinal.{0}} (hc : GxCl ρ (awAt S ρ) c) (hcV : c < awV S) (h1 : 1 ≤ gxTh ρ (awAt S ρ) c) :
    ImgPkg ρ δ (fun x => gxTh x (awAt S x) c) := by
  obtain ⟨W, Z, w, m, b⟩ := aw_img h hρS c hc hcV
  exact ⟨h1, aw_lt_δ h hρS hc, W, Z, w, m, fun A f hW hZ C => (b A f hW hZ C).2⟩

end Eps

end Googology.Trans.PoR.InaccPsi.R2.Aw
