import Googology.Trans.PoR.InaccPsi.R2.QtAt
import Googology.Trans.PoR.InaccPsi.R2.ZrLow

/-!
# AwAt: THE ATOM SYSTEM OF ALL CODES BELOW `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂)`

`θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + K_j)` (`Zr.zrK`), `K_ω = sup_j K_j = ψ_{Ω₂}(Ω_ω + Ω₂)`
(`Zr.zrK_sup`), `K⁽⁰⁾_Z = Ul.UlK S 0 Z`.  The atoms over `Z` are the strongly critical `Ω₁ < s < K_ω` in `K⁽⁰⁾_Z`.  They
form an atom system with the hull facts `Zb.ZbAS.Ok`: an atom `s` lies in every `Cl(a, b)` with `Ω_ω + s ≤ a` (its
collapse arguments are below `Ω_ω + s`: `aw_args`; the argument of an atom `ψ_{Ω₂}(Ω_ω + y) < K_ω` has `y < ψ_{Ω₂}(Ω_ω + y)`,
`Zr.zr_lt_atom`).

* `awV`, `awAt`, `zrK_lt_V`, `aw_lt_V_iff`, `aw_arg_lt_V`, `aw_lt_atom`;
* `aw_args` (**every `z < K_ω` of the notation has its collapse arguments below `Ω_ω + z`**), `aw_mem`, `aw_hull`;
* `awU` (**THE ATOM SYSTEM BELOW `K_ω`**), `awU_ok`;
* `aw_K_code`, `aw_code_K` (**below `K_ω` the codes over a strongly critical `Z` are `K⁽⁰⁾_Z`**);
* `aw_coll`, `aw_atom_form` (**an atom above `θ` is `ψ_{Ω₂}(Ω_ω + y)` with a code `0 < y < K_ω`**), `aw_atom_mem`,
  `aw_th_mem`, `aw_K_mem`.

No new axiom.  New definitions: `awV`, `awAt`, `awU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Ui

variable (S : InaccSeq.{0})

/-- `K_ω = ψ_{Ω₂}(Ω_ω + Ω₂)`. -/
noncomputable def awV : Ordinal.{0} := S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))

/-- **The atoms over `Z`**: the strongly critical `Ω₁ < s < K_ω` in `K⁽⁰⁾_Z`. -/
def awAt (Z : Ordinal.{0}) : Set Ordinal.{0} :=
  {s | SC s ∧ Om 1 < s ∧ s < awV S ∧ Ul.UlK S 0 Z s}

variable {S}

theorem awV_SC : SC (awV S) := SC_psi (InR_Om_succ 1) _

theorem awV_lt_Om2 : awV S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem aw_Om1_lt_V : Om 1 < awV S := (psiS_bounds (S := S) _ 1).1

/-- `K_j < K_ω`. -/
theorem zrK_lt_V : ∀ j, zrK S j < awV S
  | 0 => by rw [zrK_zero]; exact aw_Om1_lt_V
  | j + 1 => by
    rw [zrK_succ]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 (zrK_lt_Om2 j))
      (CSet.add_mem (ConjT.OmW_mem S _ _) (CSet.of_lt (zrK_lt_V j)))

/-- **The plateau**: `x < K_ω ⇔ x < K_j` for some `j`. -/
theorem aw_lt_V_iff {x : Ordinal.{0}} : x < awV S ↔ ∃ j, x < zrK S j :=
  ⟨fun h => zrK_sup h, fun ⟨j, h⟩ => h.trans (zrK_lt_V j)⟩

/-- The argument of an atom below `K_ω` is below `K_ω`. -/
theorem aw_arg_lt_V {y : Ordinal.{0}} (h : S.psi (Om ω + y) (Om (1 + 1)) < awV S) : y < awV S := by
  by_contra hV
  push Not at hV
  obtain ⟨j, hj⟩ := aw_lt_V_iff.1 h
  cases j with
  | zero =>
    rw [zrK_zero] at hj
    exact absurd hj (not_lt.2 (psiS_bounds (S := S) _ 1).1.le)
  | succ j =>
    rw [zrK_succ] at hj
    exact absurd hj (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1)
      (add_le_add le_rfl ((zrK_lt_V j).le.trans hV))).1)

/-- **`y < ψ_{Ω₂}(Ω_ω + y)` below `K_ω`.** -/
theorem aw_lt_atom {y : Ordinal.{0}} (h : S.psi (Om ω + y) (Om (1 + 1)) < awV S) :
    y < S.psi (Om ω + y) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := aw_lt_V_iff.1 (aw_arg_lt_V h)
  exact zr_lt_atom j y hj

/-- **Every `z < K_ω` of the notation has its collapse arguments below `Ω_ω + z`.** -/
theorem aw_args : ∀ z, z ∈ ⋃ a, S.CSet a 0 → z < awV S → uiArgs S (Om ω + z) z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzV
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hz
  have hsub : ∀ u : Term, NF u → val S u < z → uiArgsT S (Om ω + z) u := fun u hu hlt => by
    have h := IH (val S u) hlt (Set.mem_iUnion.2 (exists_mem_CSet S u)) (hlt.trans hzV)
    unfold uiArgs at h
    rw [Bc.bcNf_val S hu] at h
    exact uiArgsT_mono (add_le_add le_rfl hlt.le) u h
  have hz2 : z < Om (1 + 1) := hzV.trans awV_lt_Om2
  unfold uiArgs
  generalize Bc.bcNf S z = t at hN hv
  subst hv
  cases t with
  | zero => trivial
  | inacc n => trivial
  | inaccW => trivial
  | add a b =>
    by_cases h : val S (add a b) < Om 1
    · exact Or.inl h
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact Om_pos one_ne_zero)
    obtain ⟨hla, htb⟩ := ui_add_parts (S := S) hN
    have htl : tail (val S (add a b)) < val S (add a b) := tail_lt h0
    have hb0 : val S b ≠ 0 := Term.val_ne_zero (S := S) hN.2.1 hN.2.2.2.1
    have hal : lead (val S (add a b)) < val S (add a b) := by
      conv_rhs => rw [← lead_add_tail h0]
      rw [htb]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
    rw [hla] at hal; rw [htb] at htl
    exact Or.inr ⟨hsub a hN.1 hal, hsub b hN.2.1 htl⟩
  | phi a b =>
    by_cases h : val S (phi a b) < Om 1
    · exact Or.inl h
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    exact Or.inr ⟨hsub a hNa hav, hsub b hNb hbv⟩
  | om a =>
    by_cases h : val S (om a) < Om 1
    · exact Or.inl h
    refine Or.inr (hsub a hN.1 ?_)
    have h2 : val S a < 1 + 1 := Om_lt_Om.1 hz2
    have h2' : val S a < ω := h2.trans (by exact_mod_cast natCast_lt_omega0 2)
    exact h2'.trans_le ((omega0_le_omega 1).trans (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h))
  | psiS s a =>
    by_cases h : val S (psiS s a) < Om 1
    · exact Or.inl h
    have hsem := Term.sem_of_NF (S := S) hN
    set σ := val S s with hσ
    have hb := psiS_bounds (S := S) (val S a) σ
    have hσ1 : σ = 1 := by
      have h1 : Om σ < Om (1 + 1) := hb.1.trans hz2
      have h3 : Om 1 < Om (σ + 1) := (not_lt.1 h).trans_lt hb.2
      have ha : σ < 1 + 1 := Om_lt_Om.1 h1
      have hb' : 1 < σ + 1 := Om_lt_Om.1 h3
      have hle : σ ≤ 1 := Order.lt_add_one_iff.1 ha
      have hge : 1 ≤ σ := Order.lt_add_one_iff.1 hb'
      exact le_antisymm hle hge
    have hval : val S (psiS s a) = S.psi (val S a) (Om (1 + 1)) := by simp only [val]; rw [← hσ, hσ1]
    have hown : val S a ∈ S.CSet (val S a) (S.psi (val S a) (Om (1 + 1))) := by
      have := hsem.2.2; rw [← hσ, hσ1] at this; exact this
    have hzV' : S.psi (val S a) (Om (1 + 1)) < awV S := by rw [← hval]; exact hzV
    have haB : val S a < Om ω + Om (1 + 1) := by
      have hownV : Om ω + Om (1 + 1) ∈ S.CSet (Om ω + Om (1 + 1)) (S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) :=
        CSet.add_mem (ConjT.OmW_mem S _ _) (mxOm2_mem _ _)
      have h1 := compare_psi (InR_Om_succ 1) hown hownV
      have h2 : compare (S.psi (val S a) (Om (1 + 1))) (S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))) = Ordering.lt :=
        compare_lt_iff_lt.2 hzV'
      rw [h2] at h1
      exact compare_lt_iff_lt.1 h1.symm
    have hz0 : 0 < val S (psiS s a) :=
      lt_of_lt_of_le (Om_pos one_ne_zero) (not_lt.1 h)
    have haW : val S a < Om ω + val S (psiS s a) := by
      rcases le_or_gt (val S a) (Om ω) with h1 | h1
      · exact h1.trans_lt (lt_add_of_pos_right _ hz0)
      · obtain ⟨y, hy⟩ := exists_add_of_le h1.le
        have hzV2 : S.psi (Om ω + y) (Om (1 + 1)) < awV S := by rw [← hy]; exact hzV'
        have hyz := aw_lt_atom hzV2
        rw [← hy, ← hval] at hyz
        rw [hy]
        exact (add_lt_add_iff_left _).2 hyz
    have hs1 : σ < val S (psiS s a) := by
      rw [hσ1]; exact (Ordinal.one_lt_omega0.trans_le (omega0_le_omega 1)).trans_le
        (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h)
    have hsa := hsub s hN.1 hs1
    have hqL : val S (psiS s a) ≤ S.Lam :=
      (hz2.trans (S.Om_lt_Lam (S.add_one_lt_Lam S.one_lt_Lam))).le
    refine Or.inr ⟨haW, hsa, ui_args_hull (A := val S a) (B := Om ω + val S (psiS s a))
      (q := val S (psiS s a)) (not_lt.1 h) hqL haW.le (fun u hu _ hlt => hsub u hu hlt) a hN.2.1 ?_⟩
    rw [hval]; exact hown
  | psiI n a =>
    by_cases h : val S (psiI n a) < Om 1
    · exact Or.inl h
    exfalso
    have hfix : Om (val S (psiI n a)) = val S (psiI n a) := Om_psiI _ n
    have h2 : val S (psiI n a) < 1 + 1 := by
      have := hz2; rw [← hfix] at this; exact Om_lt_Om.1 this
    have h3 : val S (psiI n a) < ω := h2.trans (by exact_mod_cast natCast_lt_omega0 2)
    exact absurd (h3.trans_le ((omega0_le_omega 1).trans (by rw [← Om_of_ne_zero one_ne_zero]; exact not_lt.1 h)))
      (lt_irrefl _)

/-- **Hull membership of the atoms**: an atom `s` over `Z`, with every ordinal below `Z` of the notation, lies in every
`Cl(a, b)` with `Ω_ω + s ≤ a` and a strongly critical `b ∈ [Z, Ω₁]`. -/
theorem aw_mem {a b Z s : Ordinal.{0}} (ha : Om ω + s ≤ a) (hb : SC b) (hb1 : b ≤ Om 1) (hZb : Z ≤ b)
    (hZN : ∀ z < Z, z ∈ ⋃ e, S.CSet e 0) (hs : s ∈ awAt S Z) : s ∈ S.CSet a b := by
  have hsN : s ∈ ⋃ e, S.CSet e 0 :=
    (Qt.qt_N_iff S).1 (Qt.qt_K_Vals S (fun z hz => (Qt.qt_N_iff S).2 (hZN z hz)) hs.2.2.2)
  have hd : uiDat S s < b := by
    have h1 : Ul.ulD S 0 s < b := (Ul.ul_vis hb).2 (hs.2.2.2.mono hZb)
    rw [← Vd.vdD_eq] at h1
    exact (Vd.vd_dat_ui hsN hb hb1).1 h1
  have hargs : uiArgs S a s := uiArgsT_mono ha _ (aw_args s hsN hs.2.2.1)
  obtain ⟨-, hv⟩ := Bc.bcNf_spec S hsN
  have h := ui_code_mem (S := S) (A := a) (q := b) _ hd hargs
  rwa [hv] at h

/-- **THE HULL LEMMA BELOW `K_ω`**: for `Z ≤ Ω₁` with `Cl(a, Z) ∩ Ω₁ ⊆ Z`, every member of `Cl(a, Z)` below `K_ω` is a
code over the atoms `awAt Z`. -/
theorem aw_hull {a Z : Ordinal.{0}} (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x, x ∈ S.CSet a Z → x < awV S → GxCl Z (awAt S Z) x := by
  have hK : ∀ x, x ∈ S.CSet a Z → Ul.UlK S 0 Z x := Ul.ulK_hull (s := 0) fun e hea heC _ => by
    rw [zero_add]
    exact hkey _ (CSet.psi_mem hea Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) heC) (psi_lt Low.InR_Om_one _)
  have hθ2 : awV S < Om (1 + 1) := awV_lt_Om2
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxθ
  rcases lt_or_ge x (Om 1) with h1 | h1
  · exact GxCl.small (hkey x hx h1)
  have h0 : x ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans Nm.one_lt_Om1) h1).ne'
  by_cases hP : IsPrincipal (· + ·) x
  · rcases prin_mem_cases hx (hZ1.trans h1) hP h0 with
      ⟨n, rfl⟩ | rfl | ⟨p, q, hp, hq, hpx, hqx, rfl⟩ | ⟨p, hp, hpx, rfl⟩ | ⟨π, e, hπ, -, -, -, rfl⟩
    · exact absurd (hxθ.trans hθ2) (not_lt.2 (mxOm2_lt_I n).le)
    · exact absurd (hxθ.trans hθ2) (not_lt.2 mxOm2_lt_Iw.le)
    · exact GxCl.phi (IH p hpx hp (hpx.trans hxθ)) (IH q hqx hq (hqx.trans hxθ))
    · have hp1 : p ≤ 1 := le_of_Om_lt_Om_succ (hxθ.trans hθ2)
      have hp1' : 1 ≤ p := not_lt.1 fun h => absurd h1 (not_le.2 (Om_lt_Om.2 h))
      rw [le_antisymm hp1 hp1']
      exact GxCl.om
    · rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact GxCl.om
      · exact GxCl.atom ⟨SC_psi hπ e, h, hxθ, hK _ hx⟩
  · obtain ⟨hl, ht⟩ := lead_tail_mem hx h0
    have hlx : lead x < x := lt_of_le_of_ne (lead_le h0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htx : tail x < x := tail_lt h0
    rw [← lead_add_tail h0]
    exact GxCl.add (IH _ hlx hl (hlx.trans hxθ)) (IH _ htx ht (htx.trans hxθ))

variable (S)

/-- **THE ATOM SYSTEM BELOW `K_ω`.** -/
noncomputable def awU : ZbAS where
  At := awAt S
  V := awV S
  V_SC := awV_SC
  V_lt := awV_lt_Om2
  Om1_lt_V := aw_Om1_lt_V
  gxAt := fun _ s hs => ⟨hs.1, hs.2.1⟩
  mono := fun _ _ h _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.mono h⟩
  lt_V := fun _ _ hs => hs.2.2.1
  supp := fun _ _ hZ hs => by
    obtain ⟨m, hm, hk⟩ := Ul.ulK_supp hZ hs.2.2.2
    exact ⟨m + 1, hZ.isSuccLimit.add_one_lt hm, hs.1, hs.2.1, hs.2.2.1, hk⟩

theorem awU_ok : (awU S).Ok S where
  mem := fun _ _ _ _ ha hb hb1 hZb hZN hs => aw_mem ha hb hb1 hZb hZN hs
  hull := fun _ _ _ hZ1 hkey x hx hxV => aw_hull hZ1 hkey x hx hxV

instance : Fact ((awU S).Ok S) := ⟨awU_ok S⟩

theorem awU_V : (awU S).V = awV S := rfl

theorem awU_At (Z : Ordinal.{0}) : (awU S).At Z = awAt S Z := rfl

variable {S}

/-! ## The codes over `Z` and `K⁽⁰⁾_Z` -/

/-- A code is in `K⁽⁰⁾_Z`. -/
theorem aw_code_K {Z x : Ordinal.{0}} (hx : GxCl Z (awAt S Z) x) : Ul.UlK S 0 Z x := by
  induction hx with
  | small h => exact Ul.UlK.small h
  | om => exact Ul.UlK.om Ul.UlK.one
  | atom hs => exact hs.2.2.2
  | add _ _ ihx ihy => exact Ul.UlK.add ihx ihy
  | phi _ _ ihx ihy => exact Ul.UlK.phi ihx ihy

/-- **Below `K_ω` a member of `K⁽⁰⁾_Z` is a code over `Z`.** -/
theorem aw_K_code {Z x : Ordinal.{0}} (hZ : SC Z) (hx : Ul.UlK S 0 Z x) : x < awV S → GxCl Z (awAt S Z) x := by
  have hV2 : awV S < Om (1 + 1) := awV_lt_Om2
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | zero => exact fun _ => GxCl.zero hZ.1
  | inacc n => exact fun h => absurd (h.trans hV2) (not_lt.2 (mxOm2_lt_I n).le)
  | inaccW => exact fun h => absurd (h.trans hV2) (not_lt.2 mxOm2_lt_Iw.le)
  | add _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx ((left_le_veblen x y).trans_lt h)) (ihy ((right_le_veblen x y).trans_lt h))
  | @om p _ _ =>
    intro h
    have hp : p ≤ 1 := le_of_Om_lt_Om_succ (h.trans hV2)
    rcases hp.lt_or_eq with hp | rfl
    · have hp0 : p = 0 := Ordinal.lt_one_iff_zero.1 hp
      rw [hp0, Om_zero]
      exact GxCl.small ((zero_lt_one).trans (Gg.gg_one_lt_of_SC hZ))
    · exact GxCl.om
  | @coll π e hπ hπ1 hπK heK _ _ =>
    intro h
    rcases lt_trichotomy (S.psi e π) (Om 1) with h1 | h1 | h1
    · exact absurd (Low.eq_Om_one_of_psi_lt hπ h1) (by rw [zero_add] at hπ1; exact hπ1)
    · rw [h1]; exact GxCl.om
    · exact GxCl.atom ⟨SC_psi hπ e, h1, h, Ul.UlK.coll hπ hπ1 hπK heK⟩

/-- **A strongly critical member of `K⁽⁰⁾_Z` in `(Ω₁, Ω₂)` is a collapse `ψ_{Ω₂}(e)`, `e ∈ K⁽⁰⁾_Z`.** -/
theorem aw_coll {Z w : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hw : Ul.UlK S 0 Z w) :
    SC w → Om 1 < w → w < Om (1 + 1) → ∃ e, Ul.UlK S 0 Z e ∧ w = S.psi e (Om (1 + 1)) := by
  induction hw with
  | small h => exact fun _ h1 _ => absurd (h.trans_le hZ1) (not_lt.2 h1.le)
  | zero => exact fun _ h1 _ => absurd h1 (not_lt.2 zero_le)
  | inacc n => exact fun _ _ h2 => absurd h2 (not_lt.2 (mxOm2_lt_I n).le)
  | inaccW => exact fun _ _ h2 => absurd h2 (not_lt.2 mxOm2_lt_Iw.le)
  | @add x y _ _ ihx ihy =>
    intro hS h1 h2
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at hS h1 h2 ⊢
      exact ihx hS h1 h2
    · have hxlt : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
      have hye : y = x + y := by
        refine le_antisymm le_add_self ?_
        by_contra hlt
        push Not at hlt
        exact lt_irrefl _ (hS.isPrincipal hxlt hlt)
      rw [← hye] at hS h1 h2 ⊢
      exact ihy hS h1 h2
  | @phi x y _ _ ihx ihy =>
    intro hS h1 h2
    rcases (left_le_veblen x y).lt_or_eq with hx | hx
    · rcases (right_le_veblen x y).lt_or_eq with hy | hy
      · exact absurd (hS.2 x hx y hy) (lt_irrefl _)
      · rw [← hy] at hS h1 h2 ⊢
        exact ihy hS h1 h2
    · rw [← hx] at hS h1 h2 ⊢
      exact ihx hS h1 h2
  | @om p _ _ =>
    intro _ h1 h2
    have h3 : 1 < p := Om_lt_Om.1 h1
    have h4 : p < 1 + 1 := Om_lt_Om.1 h2
    exact absurd h3 (not_lt.2 (Order.lt_add_one_iff.1 h4))
  | @coll π e hπ _ _ heK _ _ =>
    intro _ h1 h2
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2; exact ⟨e, heK, rfl⟩
    · rcases ui_psi_cases (S := S) (s := 1) (e := e) one_lt_omega0 hπ hπ2 with h' | h'
      · exact absurd h1 (not_lt.2 h'.le)
      · exact absurd h2 (not_lt.2 h')

/-- **An atom above `θ` is `ψ_{Ω₂}(Ω_ω + y)` with a code `0 < y < K_ω`.** -/
theorem aw_atom_form {Z s : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hs : s ∈ awAt S Z) (hθ : ConjT.th S < s) :
    ∃ y, 0 < y ∧ y < s ∧ y < awV S ∧ GxCl Z (awAt S Z) y ∧ s = S.psi (Om ω + y) (Om (1 + 1)) := by
  obtain ⟨hSC, h1, hV, hK⟩ := hs
  obtain ⟨e, heK, rfl⟩ := aw_coll hZ1 hK hSC h1 (hV.trans awV_lt_Om2)
  have heW : Om ω < e := by
    by_contra hle
    push Not at hle
    exact absurd hθ (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) hle).1)
  obtain ⟨y, rfl⟩ := exists_add_of_le heW.le
  have hy0 : 0 < y := by
    rcases eq_or_ne y 0 with rfl | h
    · rw [add_zero] at heW; exact absurd heW (lt_irrefl _)
    · exact pos_iff_ne_zero.2 h
  have hω : Ul.UlK S 0 Z ω := by
    have := (Ul.UlK.one (S := S) (s := 0) (q := Z)).opow
    rwa [opow_one] at this
  have hyK : Ul.UlK S 0 Z y := by
    have := (Ul.ulK_dec hZ _ heK).1 (Om ω) (Ul.UlK.om hω) le_self_add
    rwa [Ordinal.add_sub_cancel] at this
  have hyV := aw_arg_lt_V hV
  exact ⟨y, hy0, aw_lt_atom hV, hyV, aw_K_code hZ hyK hyV, rfl⟩

/-- `Ω₂ ∈ K⁽⁰⁾_Z`, `Ω_ω ∈ K⁽⁰⁾_Z`. -/
theorem aw_Om2_K (Z : Ordinal.{0}) : Ul.UlK S 0 Z (Om (1 + 1)) := Ul.UlK.om (Ul.UlK.add Ul.UlK.one Ul.UlK.one)

theorem aw_OmW_K (Z : Ordinal.{0}) : Ul.UlK S 0 Z (Om ω) := by
  have := (Ul.UlK.one (S := S) (s := 0) (q := Z)).opow
  rw [opow_one] at this
  exact Ul.UlK.om this

theorem aw_ne_Om1 : Om (1 + 1 : Ordinal.{0}) ≠ Om (0 + 1) := by
  refine (Om_lt_Om.2 ?_).ne'
  rw [zero_add]; exact lt_add_one (1 : Ordinal.{0})

/-- **An atom `ψ_{Ω₂}(Ω_ω + y)` of a code `y` below `K_ω`.** -/
theorem aw_atom_mem {Z y : Ordinal.{0}} (hy : GxCl Z (awAt S Z) y) (h : S.psi (Om ω + y) (Om (1 + 1)) < awV S) :
    S.psi (Om ω + y) (Om (1 + 1)) ∈ awAt S Z :=
  ⟨SC_psi (InR_Om_succ 1) _, (psiS_bounds (S := S) _ 1).1, h,
    Ul.UlK.coll (InR_Om_succ 1) aw_ne_Om1 (aw_Om2_K Z) (Ul.UlK.add (aw_OmW_K Z) (aw_code_K hy))⟩

/-- `θ < K_ω`. -/
theorem aw_th_lt_V : ConjT.th S < awV S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Om_pos (by
    rw [one_add_one_eq_two]; exact two_ne_zero))) (ConjT.OmW_mem S _ _)

/-- **`θ` is an atom over every `Z`.** -/
theorem aw_th_mem (Z : Ordinal.{0}) : ConjT.th S ∈ awAt S Z :=
  ⟨SC_psi (InR_Om_succ 1) _, (psiS_bounds (S := S) _ 1).1, aw_th_lt_V,
    Ul.UlK.coll (InR_Om_succ 1) aw_ne_Om1 (aw_Om2_K Z) (aw_OmW_K Z)⟩

theorem aw_K_ulK (Z : Ordinal.{0}) : ∀ j, Ul.UlK S 0 Z (zrK S j)
  | 0 => by rw [zrK_zero]; exact Ul.UlK.om Ul.UlK.one
  | j + 1 => by
    rw [zrK_succ]
    exact Ul.UlK.coll (InR_Om_succ 1) aw_ne_Om1 (aw_Om2_K Z) (Ul.UlK.add (aw_OmW_K Z) (aw_K_ulK Z j))

/-- **`K_{j+1}` is an atom over every `Z`.** -/
theorem aw_K_mem (Z : Ordinal.{0}) (j : ℕ) : zrK S (j + 1) ∈ awAt S Z :=
  ⟨zrK_SC j, zrK_gt_Om1 j, zrK_lt_V _, aw_K_ulK Z _⟩

end Googology.Trans.PoR.InaccPsi.R2.Aw
