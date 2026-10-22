import Googology.Trans.PoR.InaccPsi.R2.LxZTm

/-!
# The layer `lxZLay K` of the terms `LxZTm K`: top `e^K_x(x) = ϑˣ(Ω₁ + E_K(x) + x)`, generically in `K`

For every layer `K` with `LxZK K` (`R2.LxZE`):

* `lxzPkg` (**IMG**: from `lxzt_img` with `lxBase_ri`), `lxzRs` (**RS**: `rs_rstF` with EXACT, and `rs_rstT` for the
  constant terms);
* `lxZSys K` (**the term system**, top `e_x(x)`), `lxZLay K` (**the layer**: `E(x) = e_x(x)`, EXACT of the top
  `lxZE_piTop`, the witness pair of the top from `LxZW.lxZE_imgTop`), `lxZLay_EK` (`E(x) = e_x(x)` is an `ε`-number,
  so the generic step `lxNext` of `R2.LxEp` applies on top of it).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly LxZTm

variable {K : XtLay}

/-- **Lemma IMG for the terms of `LxZTm K`** (the package). -/
theorem lxzPkg (hZ : LxZK K) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (t : LxZTm K)
    (hCB : CBt t (upsilon l)) (h1 : 1 ≤ val t (upsilon l))
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val t) := by
  classical
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have htop := lxzt_lt_top hZ hρE hρ1 t hCB
  obtain ⟨W, Z, t', I⟩ := lxzt_img hZ R (lxBase_ri hZ.ek hl hl1 R) (val t (upsilon l)) htop
  have hwc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (cs t).toFinset :=
    ⟨by simp, fun z hz => cbt_cst t _ hCB z (List.mem_toFinset.1 hz), by simp⟩
  have hw := I.1.union hwc
  rw [Finset.union_empty] at hw
  refine ⟨h1, htop.trans (LxZW.lxZE_lt_δ hZ R le_rfl), W, Z ∪ (cs t).toFinset, hw, ?_, fun A f hW hZ' C => ?_⟩
  · rcases Finset.mem_union.1 I.2.2.2.2.1 with h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
  have hZ1 : ↑Z ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
  have htA : ∀ c ∈ cs t, c ∈ A := fun c hc => hZ' (by simp [hc])
  have ht'A : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (I.2.2.1 c hc))
  have heq := lxzt_val_fρ hZ R C hCB I.2.1 htA ht'A I.2.2.2.1.symm
  rw [heq]
  exact I.2.2.2.2.2 A f hW hZ1 C

/-- **Lemma RS for the terms of `LxZTm K`.** -/
theorem lxzRs (hZ : LxZK K) {l : Ordinal.{0}} (t : LxZTm K) (hCB : CBt t (upsilon l)) :
    RsStep l (val t) := by
  classical
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  by_cases hρs : upsilon l ≤ val t (upsilon l)
  · have hnx := upsilon_isNext l
    have hCs : ∀ σ, (∀ c ∈ (cs t).toFinset, c < σ) → CBt t σ := fun σ hσ =>
      cbt_iff t _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
    refine rs_rstF (T := val t) (C := (cs t).toFinset) R
      (fun c hc => cbt_cst t _ hCB c (List.mem_toFinset.1 hc)) hρs ?_ ?_ ?_ htg
    · exact (lxzt_lt_top hZ hρE hρ1 t hCB).trans (lxzTop_lt_ups hZ hρE hρ1 hnx.1 hnx.2.1)
    · intro σ hσ hB hCσ _
      exact (lxzt_pi hZ hσ R.ρU hB t (hCs σ hCσ)).2
    · intro σ hσE hσρ _ hCσ
      have hσ1 := hσρ.trans hρ1
      exact (lxzt_lt_top hZ hσE hσ1 t (hCs σ hCσ)).trans (lxzTop_lt_ups hZ hσE hσ1 hσρ R.ρU)
  · have hconst : ∀ x y, val t x = val t y := by
      rcases lxzt_small hZ t with hc | hc
      · exact hc
      · exact absurd (hc _ hρE hρ1 hCB) hρs
    set c := val t (upsilon l) with hc
    have e : val t = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, hconst y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have := rs_rstT R hcb htg
    rwa [OT.ev_k] at this

theorem lxzTop_lt_next (hZ : LxZK K) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    lxZE K (upsilon l) (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (lxzTop_lt_ups hZ (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `lxZSys K`**: the terms of `LxZTm K`, top `e_x(x) = ϑˣ(Ω₁ + E_K(x) + x)`. -/
noncomputable def lxZSys (K : XtLay) (hZ : LxZK K) : XtSys where
  Tm := LxZTm K
  val := LxZTm.val
  CB := CBt
  cs := LxZTm.cs
  cst := fun c => ex (LxTm.bs (K.sys.cst c))
  top := fun x => lxZE K x x
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun c x => K.sys.val_cst c x
  cb_cstI := fun c x h => K.sys.cb_cstI c x h
  lt_top := fun l hl hl1 t hCB => lxzt_lt_top hZ (ups_inE hl) (ups_lt_Om1 l hl1) t hCB
  one_le_top := fun l hl hl1 =>
    one_le_iff_pos.2 (lxZE_facts hZ (ups_inE hl) (ups_lt_Om1 l hl1) le_rfl).2.2.2.2.2.1.pos
  rep := fun l hl hl1 v hv => lxzt_rep hZ (ups_inE hl) (ups_lt_Om1 l hl1) (lxRep_ri hZ.ek hl hl1) v hv
  top_lt := fun _ hl hl1 => lxzTop_lt_next hZ hl hl1
  pkg := fun _ hl hl1 t hCB h1 R => lxzPkg hZ hl hl1 t hCB h1 R
  rs := fun _ _ _ t hCB => lxzRs hZ t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lxzt_pi hZ hσ hρ hB t ht) (lxzt_pi hZ hσ hρ hB u hu)
  small := lxzt_small hZ

theorem lxZSys_top (K : XtLay) (hZ : LxZK K) (x : Ordinal.{0}) : (lxZSys K hZ).top x = lxZE K x x := rfl

/-- **The layer `lxZLay K`**: `E(x) = e_x(x)`. -/
noncomputable def lxZLay (K : XtLay) (hZ : LxZK K) : XtLay where
  sys := lxZSys K hZ
  E := fun x => lxZE K x x
  top_eq := fun _ hx hx1 => (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.2.1.symm
  exp_dvd := fun _ hx hx1 => opow_dvd_of_inE (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.2.1
    (lxZE_facts hZ hx hx1 le_rfl).2.2.2.1.le
  exp_lt := fun _ hx hx1 => lxzTop_lt_Om1 hZ hx hx1
  top_gt := fun _ hx hx1 => (lxZE_facts hZ hx hx1 le_rfl).2.2.2.1
  top_lt_ups := fun _ _ hx hx1 hxu hu => lxzTop_lt_ups hZ hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 t ht => lxzt_lt_top hZ hx hx1 t ht
  exact := fun _ _ hσ hρ hB t ht => lxzt_pi hZ hσ hρ hB t ht
  exp_pi := fun _ _ hσ hρ hB => lxZE_piTop hZ hσ hρ hB
  top_wit := fun ρ _ _ h => by
    obtain ⟨W, Z, hw, hTW, hI⟩ := LxZW.lxZE_imgTop hZ h
    have hρE := h.ρE
    have hρ1 := h.ρ1
    refine ⟨W, Z, hw, hTW, fun A f hW hZ' C => ?_⟩
    obtain ⟨hE, hle⟩ := hI A f hW hZ' C
    have hρe : ρ < lxZE K ρ ρ := (lxZE_facts hZ hρE hρ1 le_rfl).2.2.2.1
    exact ⟨⟨f (lxZE K ρ ρ), hE.symm, opow_dvd_of_inE hE (C.mono C.rho (hW hTW) hρe).le⟩, hle⟩

theorem lxZLay_E (K : XtLay) (hZ : LxZK K) (x : Ordinal.{0}) : (lxZLay K hZ).E x = lxZE K x x := rfl

/-- **The top of `lxZLay K` is an `ε`-number**, so the generic step `lxNext` applies on top of it. -/
theorem lxZLay_EK (K : XtLay) (hZ : LxZK K) : LxEK (lxZLay K hZ) := fun _ hx hx1 =>
  (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.2.1

end Googology.Trans.PoR.InaccPsi.R2.Lx
