import Googology.Trans.PoR.InaccPsi.R2.GeUnif

/-!
# WHERE THE FRONTIERS LIE, for every code below `Ω₁^ω`: `Λ⁺(geB a) = ι(Γ_{Ω₁+2+a}·ω)` and the supremum `ι(Γ_{Ω₁+Ω₁^ω})`

For a code `a < Ω₁^ω` whose digits lie below `ε₀` (so its gate lies below every base), the gated layer `geB a`
(`R2.GeTow`) is an ungated layer `geLX a` (`geLayX`); its top reads the atom `Γ_{Ω₁+1+(1+a)}` and it has terms for every
code below it (`R2.GeUnif.geB_codes`), so the frontier lemma `R2.GeFr.geB1_eq` locates its frontier:

* `geSysX`, `geLayX` (**a gated layer whose gate lies below `ε₀` is a layer**), `geX a`, `geLX a`;
* `geLoc` (**`Λ⁺(geX a) = ι(Γ_{Ω₁+2+a}·ω)`, `ρ` of it `= P(…) < L(0)`**), `geFix` (THEOREM UNI at the fixed range
  restarts below it), `geEnum` (**ENUM-REACH at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed points
  included**), `geCapV` (**CapV there**), `geBlk` (**BLK^O and the exact reaches below `υ` of it**);
* `geFam` (the family of the layers of the codes `Ω₁^{k+1}`), `geFam_sup` (**`sup_a Λ⁺(geX a) = ι(Γ_{Ω₁+Ω₁^ω})`, `υ` of
  it `= P(Γ_{Ω₁+Ω₁^ω}) < L(0)`**), `geFam_enum`, `geFam_capV`, `geFam_blk`, `geFam_road` (**THE ROAD with UPPER, LOWER
  and CapV asked only at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})`**), `ge_fr_order` (**`ι(Γ_{Ω₁·2+1}) < ι(Γ_{Ω₁+2+a}·ω) < ι(Γ_{Ω₁+Ω₁^ω})
  < ι(Ω₂)`, `P(Γ_{Ω₁+Ω₁^ω}) < L(0)`**).

No new axiom.  New definitions: `geSysX`, `geLayX`, `geX`, `geLX`, `geFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## A gated layer whose gate lies below `ε₀` is a layer -/

theorem ge_gx {g x : Ordinal.{0}} (hg : g < ε₀) (hx : InE x) : g < x := hg.trans_le (gc_eps0_le hx)

/-- **A gated term system whose gate lies below `ε₀`** is a term system (every base is above the gate). -/
noncomputable def geSysX {g : Ordinal.{0}} (X : GdSys g) (hg : g < ε₀) : XtSys where
  Tm := X.Tm
  val := X.val
  CB := X.CB
  cs := X.cs
  cst := X.cst
  top := X.top
  cb_cst := X.cb_cst
  cb_iff := X.cb_iff
  val_cst := X.val_cst
  cb_cstI := X.cb_cstI
  lt_top := fun l hl hl1 => X.lt_top l hl hl1 (ge_gx hg (ups_inE hl))
  one_le_top := fun l hl hl1 => X.one_le_top l hl hl1 (ge_gx hg (ups_inE hl))
  rep := fun l hl hl1 => X.rep l hl hl1 (ge_gx hg (ups_inE hl))
  top_lt := fun l hl hl1 => X.top_lt l hl hl1 (ge_gx hg (ups_inE hl))
  pkg := fun l hl hl1 => X.pkg l hl hl1 (ge_gx hg (ups_inE hl))
  rs := fun l hl hl1 => X.rs l hl hl1 (ge_gx hg (ups_inE hl))
  uni_le := fun σ ρ hσ hρ hB => X.uni_le σ ρ hσ hρ hB (ge_gx hg hB.1)
  small := fun t => (X.small t).imp id fun h x hx hx1 hc => h x hx hx1 (ge_gx hg hx) hc

/-- **A gated layer whose gate lies below `ε₀`** is a layer. -/
noncomputable def geLayX {g : Ordinal.{0}} (L : GdLay g) (hg : g < ε₀) : XtLay where
  sys := geSysX L.sys hg
  E := L.E
  top_eq := fun x hx hx1 => L.top_eq x hx hx1 (ge_gx hg hx)
  exp_dvd := fun x hx hx1 => L.exp_dvd x hx hx1 (ge_gx hg hx)
  exp_lt := fun x hx hx1 => L.exp_lt x hx hx1 (ge_gx hg hx)
  top_gt := fun x hx hx1 => L.top_gt x hx hx1 (ge_gx hg hx)
  top_lt_ups := fun x u hx hx1 => L.top_lt_ups x u hx hx1 (ge_gx hg hx)
  lt_top_E := fun x hx hx1 => L.lt_top_E x hx hx1 (ge_gx hg hx)
  exact := fun σ ρ hσ hρ hB => L.exact σ ρ hσ hρ hB (ge_gx hg hB.1)
  exp_pi := fun σ ρ hσ hρ hB => L.exp_pi σ ρ hσ hρ hB (ge_gx hg hB.1)
  top_wit := fun ρ τ δ h => by
    classical
    have hgρ : g < ρ := ge_gx hg (upsPt_inE h.ρU)
    obtain ⟨W, Z, hw, hm, hI⟩ := L.top_wit ρ τ δ h hgρ
    refine ⟨W, insert g Z, hw.insZ hgρ, hm, fun A f hW hZ C => ?_⟩
    have hgA : g ∈ A := hZ (by simp)
    exact hI A f hW (fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))) ⟨C, hgA⟩

/-! ## The layer of a code with small digits -/

/-- **The layer of the code `a`** (digits below `ε₀`), ungated. -/
noncomputable def geLX {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : XtLay := geLayX (geB a ha).K
    (by rw [geB_g]; exact hg)

/-- Its term system. -/
noncomputable def geX {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : XtSys := (geLX ha hg).sys

theorem geX_top {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (geX ha hg).top x = gq (1 + sbc a x) x :=
  geB_top ha hx hx1 (ge_gx hg hx)

theorem geX_pkg {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : XtTopPkg (geX ha hg) := XtLay.topPkg (geLX ha hg)

theorem geT_lt {a : Ordinal.{0}} (ha : a < geW) : 1 + a < geW := geW_indec.add_lt
    ((Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_W) ha

theorem geT_le {a : Ordinal.{0}} (ha : a < geW) : gcG (1 + a) ≤ geV := (gcG_lt (geT_lt ha)).le

theorem geX_cl {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : ∀ Z, SC Z → GxCl Z (geAt Z) (gcG
    (1 + a)) := fun Z hZ => by
  obtain ⟨h1, h2⟩ := gate_one_add ha hZ.isSuccLimit (ge_gx hg (gg_SC_eps hZ))
  exact GxCl.atom (geG_atom h1 h2)

theorem geX_poly {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) : GePoly (geX ha hg) (gcG
    (1 + a)) := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := (geB_codes S a ha).2 (max Z ε₀) c (by rw [geB_g]; exact hg.trans_le (le_max_right _ _))
    (geCl_mono (le_max_left _ _) hc) hcE
  exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (max_le hZy (gc_eps0_le (gg_SC_eps hy)))⟩

theorem geX_topth {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) : ∀ y, SC y → y < Om 1 →
    (geX ha hg).top y = gxTh y (geAt y) (gcG (1 + a)) := by
  intro y hy hy1
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  rw [geX_top ha hg hyE hy1', ← geB_E ha hyE hy1' (ge_gx hg hyE)]
  exact (geB_codes S a ha).1 y hy hy1 (ge_gx hg hyE)

theorem geX_topE {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : ∀ x, InE x → x < Om1 → eN x <
    (geX ha hg).top x := by
  intro x hx hx1
  rw [geX_top ha hg hx hx1]
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine (geq_eN_le hx hx1 h0T (hx.pos.trans hx1)).trans_lt (geq_lt hx hx1 (geO_lt ha hx (ge_gx hg hx)) ?_)
  exact lt_of_lt_of_le zero_lt_one le_self_add

theorem geG_E (c : Ordinal.{0}) : ω ^ gcG c = gcG c := Low.opow_eq_self_of_SC (gcG_SC c)

/-- **WHERE THE FRONTIER OF THE CODE `a` LIES**: `Λ⁺(geX a) = ι(Γ_{Ω₁+2+a}·ω)`, `ρ` of it `= P(…) < L(0)`. -/
theorem geLoc {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) :
    xtB1 (geX ha hg) = iota S (gcG (1 + a) * ω) ∧
    upsilon (xtB1 (geX ha hg)) = Pv S (gcG (1 + a) * ω) ∧ Pv S (gcG (1 + a) * ω) < Nc.ncL S 0 := by
  have h := geB1_eq (S := S) (geT_le ha) (geX_poly ha hg S) (geX_topth ha hg S) (geX_cl ha hg) (gcG_Om1_lt _).le
    (geX_topE ha hg) (geX_pkg ha hg)
  rwa [geG_E] at h

/-- **`Θ_F(m_F) = O_a(F)` at every fixed range restart below `Λ⁺(geX a)`** (THEOREM UNI). -/
theorem geFix {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < xtB1 (geX ha hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (geX ha hg) l := by
  have hlt : l < iota S (ω ^ gcG (1 + a) * ω) := by rw [geG_E, ← (geLoc ha hg S).1]; exact hl
  exact geUniTh (geT_le ha) (geX_poly ha hg S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem geX_nonfix {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) : XtNonfix (xtOrec (geX ha hg)) (xtB1
    (geX ha hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (geX_pkg ha hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed points included.** -/
theorem geEnum {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (1 + a) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (geLoc ha hg S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (geX_pkg ha hg)) (geX_nonfix ha hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (geX_pkg ha hg)) hr.1 hl).2 (geFix ha hg S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed points included.** -/
theorem geCapV {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (1 + a) * ω)) :
    CdCapV S l := by
  have hl' := hl
  rw [← (geLoc ha hg S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (geX_pkg ha hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (geX_nonfix ha hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (geX_pkg ha hg) hr hl' hfx.symm (geEnum ha hg S hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(geX a)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O_a(λ)`. -/
theorem geBlk {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) :
    (∀ c d, c < d → d < upsilon (xtB1 (geX ha hg)) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (geX ha hg) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (geX ha hg) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (geX ha hg) l)) ∧
    (∀ α < upsilon (xtB1 (geX ha hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (geX_pkg ha hg)

/-! ## The family of the codes `Ω₁^{k+1}` and the supremum `ι(Γ_{Ω₁+Ω₁^ω})` -/

theorem gate_oP (k : ℕ) : gate (oP k) = 1 := by
  have h : oP k < oP (k + 1) := by
    rw [oP_succ]; exact lt_mul_of_one_lt_right (pos_iff_ne_zero.2 (oP_ne k)) (Lu.lu_one_lt_E Rj.rj_Om1_inE)
  rw [(sbc_eq h 0).2]
  show max (oP k / oP k) (gtN k (oP k % oP k)) = 1
  rw [Ordinal.div_self (oP_ne k), Ordinal.mod_self, gtN_zero_code]
  exact max_eq_left zero_le

theorem oP_lt_W (k : ℕ) : oP k < geW := lt_W_iff.2 ⟨k + 1, by
  rw [oP_succ]; exact lt_mul_of_one_lt_right (pos_iff_ne_zero.2 (oP_ne k)) (Lu.lu_one_lt_E Rj.rj_Om1_inE)⟩

theorem gate_oP_lt (k : ℕ) : gate (oP k) < ε₀ := by
  rw [gate_oP]; exact_mod_cast natCast_lt_epsilon 1 0

/-- The `k`-th member of the family: the code `Ω₁^{k+1}`. -/
noncomputable def geXk (k : ℕ) : XtSys := geX (oP_lt_W (k + 1)) (gate_oP_lt (k + 1))

theorem oP_strictMono : StrictMono oP := strictMono_nat_of_lt_succ fun k => by
  rw [oP_succ]; exact lt_mul_of_one_lt_right (pos_iff_ne_zero.2 (oP_ne k)) (Lu.lu_one_lt_E Rj.rj_Om1_inE)

theorem geGood_mul (c : Ordinal.{0}) (hc : c < geW) (hgc : gate c < ε₀) (S : InaccSeq.{0}) :
    Bt.Good S (gcG c * ω) := by
  refine ge_good fun Z hZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (GxCl.atom (geG_atom hc (ge_gx hgc (gg_SC_eps hZ))))
    (GxCl.small (gg_one_lt_of_SC hZ)))

theorem geW_lim : IsSuccLimit geW := by
  have h1 : (1 : Ordinal.{0}) < geW := (Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_W
  refine Ordinal.isSuccLimit_iff.2 ⟨(zero_lt_one.trans h1).ne', isSuccPrelimit_of_succ_lt fun b hb => ?_⟩
  rw [succ_eq_add_one]; exact geW_indec.add_lt hb h1

/-- **The family of the layers of the codes `Ω₁^{k+1}`.** -/
noncomputable def geFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (geXk k)
  off := fun k => xtOrec (geXk k)
  spec := fun k => xtSpec1 (geX_pkg _ _)
  mono := fun k => by
    show xtB1 (geXk k) < xtB1 (geXk (k + 1))
    unfold geXk
    rw [(geLoc _ _ S).1, (geLoc _ _ S).1]
    have hc : 1 + oP (k + 1) < geW := geT_lt (oP_lt_W (k + 1))
    have hg1 : gate (1 + oP (k + 1)) < ε₀ := by
      rw [one_add_of_omega0_le ((omega0_lt_inE Rj.rj_Om1_inE).le.trans
        ((show Om1 = oP 1 by unfold oP; simp) ▸ oP_strictMono.monotone (by omega)))]
      exact gate_oP_lt _
    refine cd_iota_lt_of_good (geGood_mul _ hc hg1 S) ?_
    have hlt : 1 + oP (k + 1) < 1 + oP (k + 1 + 1) := (add_lt_add_iff_left 1).2 (oP_strictMono (by omega))
    have hE := geG_E (1 + oP (k + 1 + 1))
    exact (InE.mul_lt hE (gcG_lt hlt) (omega0_lt_inE hE)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => geX_nonfix _ _

/-- **`sup_k Λ⁺(geX Ω₁^{k+1}) = ι(Γ_{Ω₁+Ω₁^ω})`, `υ` of it `= P(Γ_{Ω₁+Ω₁^ω}) < L(0)`.** -/
theorem geFam_sup (S : InaccSeq.{0}) : (geFam S).famSup = iota S geV ∧ upsilon (geFam S).famSup = Pv S geV ∧
    Pv S geV < Nc.ncL S 0 := by
  have hVS := geV_SC
  have hVE : ω ^ geV = geV := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < geW → gcG c * ω < geV := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (geFam S).famSup = iota S geV := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (geXk k) ≤ _
      unfold geXk
      rw [(geLoc _ _ S).1]
      exact iota_mono _ _ (hstep _ (geT_lt (oP_lt_W (k + 1)))).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit geW_lim e.2
      obtain ⟨n, hn⟩ := lt_W_iff.1 hc
      have hcn : c < 1 + oP (n + 1) := (hn.trans (oP_strictMono (Nat.lt_succ_self n))).trans_le le_add_self
      have h1 : e.1 < gcG (1 + oP (n + 1)) * ω :=
        (hec.trans (gcG_lt hcn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (1 + oP (n + 1)) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (geXk n) := (geLoc _ _ S).1.symm
        _ ≤ (geFam S).famSup := ((geFam S).famBd_lt n).le
  have hups : upsilon (geFam S).famSup = Pv S geV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (geV_lt_Om2 S).le⟩

theorem geFam_fix (S : InaccSeq.{0}) : (geFam S).famTHfix S :=
  fun k _ hr hlk hfix => geFix _ _ S hr hlk hfix

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+Ω₁^ω})`, fixed points included.** -/
theorem geFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S geV) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (geFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (geFam S).famLt hl
  have hk' : l < iota S (gcG (1 + oP (k + 1)) * ω) := by
    have := (geLoc (oP_lt_W (k + 1)) (gate_oP_lt (k + 1)) S).1
    rw [← this]; exact hk
  exact geEnum (oP_lt_W (k + 1)) (gate_oP_lt (k + 1)) S hr hk'

/-- **CapV at every range restart below `ι(Γ_{Ω₁+Ω₁^ω})`, fixed points included.** -/
theorem geFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S geV) :
    CdCapV S l := by
  rw [← (geFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (geFam S).famLt hl
  have hk' : l < iota S (gcG (1 + oP (k + 1)) * ω) := by
    have := (geLoc (oP_lt_W (k + 1)) (gate_oP_lt (k + 1)) S).1
    rw [← this]; exact hk
  exact geCapV (oP_lt_W (k + 1)) (gate_oP_lt (k + 1)) S hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+Ω₁^ω})} = P(Γ_{Ω₁+Ω₁^ω})`**, with the exact reaches. -/
theorem geFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (geFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (geFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (geFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (geFam S).off k l)) ∧
    (∀ α < upsilon (geFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (geFam S).famBlk

/-- **THE ROAD past every code below `Ω₁^ω`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+Ω₁^ω})` (CapV also
`υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem geFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S geV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S geV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S geV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (geFam_sup S).1
  refine (geFam S).famRoad3 (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h)) (geFam_fix S)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (geFam S).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact geFam_capV S hr (hF ▸ h)

/-- **The order of the frontiers**: `ι(Γ_{Ω₁·2+1}) < ι(Γ_{Ω₁+2+a}·ω) < ι(Γ_{Ω₁+Ω₁^ω}) < ι(Ω₂) < ι(Ω_ω)`, and
`P(Γ_{Ω₁+Ω₁^ω}) < P(Ω₂) < L(0)`, for every code `Ω₁ + 1 ≤ a < Ω₁^ω` with digits below `ε₀`. -/
theorem ge_fr_order {a : Ordinal.{0}} (ha : a < geW) (hg : gate a < ε₀) (S : InaccSeq.{0}) (hOa : Om1 + 1 ≤ a) :
    iota S gdV < iota S (gcG (1 + a) * ω) ∧ iota S (gcG (1 + a) * ω) < iota S geV ∧
      iota S geV < iota S (Om (1 + 1)) ∧ Pv S geV < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hO1 : Om1 + 1 < geW := Om1_succ_lt_W
  have hgO1 : gate (Om1 + 1) < ε₀ := by
    refine (sb_succ hO1 0).2.2.trans_lt ?_
    rw [(sb_Om1 0).2]
    exact_mod_cast natCast_lt_epsilon 2 0
  have hgV : Bt.Good S gdV := ge_good fun Z hZ => by
    have e : gdV = gcG (Om1 + 1) := by unfold gdV; rw [Br.Om1_eq]
    rw [e]; exact GxCl.atom (geG_atom hO1 (ge_gx hgO1 (gg_SC_eps hZ)))
  have hc := geT_lt ha
  have hg1 : gate (1 + a) < ε₀ := (gate_one_add ha gc_eps0_lim hg).2
  have hVE : ω ^ geV = geV := Low.opow_eq_self_of_SC geV_SC
  have hgeV : Bt.Good S geV := by
    show geV ∈ S.CSet (ConjT.Aη S geV + 1) (S.psi (ConjT.Aη S geV) (Om 1))
    have := CSet.psi_mem (S := S) (a := ConjT.Aη S geV + 1) (b := S.psi (ConjT.Aη S geV) (Om 1))
      (ge_W_lt_A1 (S := S) geV) (InR_Om_succ 1) (ga_Om2_mem _ _) (geW_inC (S := S))
    rwa [geV_psi S] at this
  have hla : gdV < gcG (1 + a) * ω := by
    have e : gdV = gcG (Om1 + 1) := by unfold gdV; rw [Br.Om1_eq]
    rw [e]
    exact (gcG_le (hOa.trans le_add_self)).trans_lt
      (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  have h1 : iota S gdV < iota S (gcG (1 + a) * ω) := cd_iota_lt_of_good hgV hla
  have h2 : iota S (gcG (1 + a) * ω) < iota S geV :=
    cd_iota_lt_of_good (geGood_mul _ hc hg1 S) (InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE))
  have h3 : iota S geV < iota S (Om (1 + 1)) := cd_iota_lt_of_good hgeV (geV_lt_Om2 S)
  have h4 : Pv S geV < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h1, h2, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Ge
