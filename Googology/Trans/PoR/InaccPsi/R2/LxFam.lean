import Googology.Trans.PoR.InaccPsi.R2.LxEp
import Googology.Trans.PoR.InaccPsi.R2.LxE
import Googology.Trans.PoR.InaccPsi.R2.LqBN

/-!
# THE GENERIC STEP ON CODES and the layers `K_n` with tops `ε_{Γ(x)+n}`, up to `ι(ε_{Γ_{Ω₁+1}+ω})`

**The generic step on codes** (`lxNextPoly`, `lxNextTop`): if a layer `K` with an `ε`-number top has terms for every
code below `c` (`LgPoly K c`, `R2.LgUni`) and `E_K(y) = Θ'_y(c)`, then `lxNext K` (`R2.LxEp`) has terms for every code
below `ε_{c+1}` and top `Θ'_y(ε_{c+1})`:

* `lxTh_eN` (**`Θ'_y(ε_{c+1}) = ε_{Θ'_y(c)+1}`**: `Θ'_y` is strictly increasing on the codes, onto an initial
  segment, and keeps `ω^·`);
* `lxExpTm` (**every code `d < ε_{c+1}` is the value `Θ'_y(d)` of one exponent term `LxTm K`**: below `c` by `LgPoly`,
  `c` itself by the atom, above `c` by `d = ω^{log d} + r`, `lgDec`), `lxGt_of_ref`, `lxCNF` (the Cantor normal form of
  a code as an exponent list);
* `lxNextPoly`, `lxNextTop`.

**The layers** `lxK n` (`lxK 0 = lgLay`, `lxK (n+1) = lxNext (lxK n)`): `E_n(x) = lxG n x` (`= Γ(x)` for `n = 0`,
`ε_{Γ(x)+n}` above), code `lxC n = ε_{Γ_{Ω₁+1}+n}` (`= veblen 1 (Γ_{Ω₁+1} + n)`).  For every `n`:

* `lxK_poly` (**`LgPoly (lxK n) (lxC n)`, top `Θ'_y(lxC n)`**), `lxK_loc` (**`Λ⁺(lxK n) = ι(ε_{Γ_{Ω₁+1}+n}·ω)`, `ρ` of
  it `= P(…) < L(0)`**), `lxKT_fix`, `lxKEnum` (**ENUM-REACH at every restart of the range below `Λ⁺(lxK n)`**, fixed
  points included), `lxK_capV`, `lxK_blk` (BLK^O and the exact reaches below `υ_{Λ⁺(lxK n)}`), `lxKRoad`;
* the chain (`lxK_topIn`, `lxLam_lt`, `lxK_eq`), the family `lxFam`, `lxFam_loc` (**`sup_n Λ⁺(lxK n) =
  ι(ε_{Γ_{Ω₁+1}+ω})`, `ρ` of it `< L(0)`**), `lxFamEnum`, `lxFam_capV`, `lxFam_blk`, `lxFamRoad`, `lxFam_fr_order`,
  `lxBN_lt_K1` (the previous frontier `sup_n Λ⁺(lqBN n)` lies below `Λ⁺(lxK 1)`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The reading of `ε_{c+1}` -/

/-- **`Θ'_y(ε_{c+1}) = ε_{Θ'_y(c)+1}`** for codes `c`, `ε_{c+1}` over a strongly critical `y`. -/
theorem lxTh_eN {y c : Ordinal.{0}} (hy : SC y) (hc : LgCl y c) (hec : LgCl y (eN c)) :
    lgTh y (eN c) = eN (lgTh y c) := by
  have h1 : ω ^ eN c = eN c := eN_E c
  have hE : ω ^ lgTh y (eN c) = lgTh y (eN c) := by rw [← lgTh_opow hy hec, h1]
  have hlt : lgTh y c < lgTh y (eN c) := lgTh_lt hc (lt_eN c)
  refine le_antisymm ?_ (eN_le hlt hE)
  by_contra hgt
  push Not at hgt
  obtain ⟨d, hd, hdc, hdv⟩ := lgTh_onto hgt
  have hdE : ω ^ d = d := by
    by_contra hne
    have hlt2 : d < ω ^ d := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (Ne.symm hne)
    have h2 := lgTh_lt hd hlt2
    have h3 : ω ^ eN (lgTh y c) = eN (lgTh y c) := eN_E _
    rw [lgTh_opow hy hd, hdv, h3] at h2
    exact lt_irrefl _ h2
  have hcd : c < d := by
    by_contra hle
    push Not at hle
    have h2 := lgTh_mono (y := y) hle
    rw [hdv] at h2
    exact absurd (lt_eN (lgTh y c)) (not_lt.2 h2)
  exact absurd (eN_le hcd hdE) (not_le.2 hdc)

/-! ## Exponent terms for the codes below `ε_{c+1}` -/

section Codes

variable {K : XtLay}

/-- **Every code `d < ε_{c+1}` is read by one exponent term of `LxTm K`** (`K` with terms for the codes below `c` and
`E_K = Θ'(c)`). -/
theorem lxExpTm {c Z : Ordinal.{0}} (hZ : SC Z) (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y c)
    (hP : LgPoly K.sys c) : ∀ d, LgCl Z d → d < eN c →
      ∃ t : LxTm K, ∀ y, SC y → y < Om 1 → Z ≤ y → t.CBt y ∧ t.val y = lgTh y d := by
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hd hdc
  rcases lt_trichotomy d c with hlt | rfl | hgt
  · obtain ⟨s, hs⟩ := hP Z d hd hlt
    exact ⟨LxTm.bs s, fun y hy hy1 hZy => hs y hy hy1 hZy⟩
  · exact ⟨LxTm.tp, fun y hy hy1 _ => ⟨trivial, hE y hy hy1⟩⟩
  · have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hgt).ne'
    obtain ⟨hsub, hlog⟩ := lgDec hZ d hd
    set L := log ω d with hL
    have hwd : ω ^ L ≤ d := opow_log_le_self ω hd0
    have hwL : LgCl Z (ω ^ L) := LgCl.opow hZ.1 hlog
    have hr := hsub _ hwL hwd
    have hdec : ω ^ L + (d - ω ^ L) = d := Ordinal.add_sub_cancel_of_le hwd
    rcases eq_or_ne (d - ω ^ L) 0 with hr0 | hr0
    · have hdw : ω ^ L = d := by rw [← hdec, hr0, add_zero]
      have hLd : L < d := by
        refine lt_of_le_of_ne ((right_le_opow L one_lt_omega0).trans hdw.le) (fun e => ?_)
        have hdd : ω ^ d = d := by
          calc ω ^ d = ω ^ L := by rw [e]
            _ = d := hdw
        exact absurd (eN_le hgt hdd) (not_le.2 hdc)
      obtain ⟨t, ht⟩ := IH L hLd hlog (hLd.trans hdc)
      refine ⟨LxTm.pw t, fun y hy hy1 hZy => ⟨(ht y hy hy1 hZy).1, ?_⟩⟩
      rw [LxTm.val_pw, (ht y hy hy1 hZy).2, ← lgTh_opow hy (hlog.mono hZy), hdw]
    · have h1 : ω ^ L < d := by
        rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
      have h2 : d - ω ^ L < d := lg_sub_log_lt hd0
      obtain ⟨t1, ht1⟩ := IH _ h1 hwL (h1.trans hdc)
      obtain ⟨t2, ht2⟩ := IH _ h2 hr (h2.trans hdc)
      refine ⟨LxTm.sm t1 t2, fun y hy hy1 hZy => ⟨⟨(ht1 y hy hy1 hZy).1, (ht2 y hy hy1 hZy).1⟩, ?_⟩⟩
      rw [LxTm.val_sm, (ht1 y hy hy1 hZy).2, (ht2 y hy hy1 hZy).2, ← lgTh_add hy (hwL.mono hZy), hdec]

/-- The order of two exponent terms at one `υ`-point base above their constants is their order at every such base. -/
theorem lxGt_of_ref (hK : LxEK K) {t u : LxTm K} {k k' ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρ1 : ρ < Om1)
    (ht : t.CBt ρ) (hu : u.CBt ρ) (hlt : u.val ρ < t.val ρ) : LxGt (t, k) (u, k') := by
  intro y hyU hy1 hct hcu
  have hty : t.CBt y := LxTm.cbt_iff t ρ y ht hct
  have huy : u.CBt y := LxTm.cbt_iff u ρ y hu hcu
  rcases lt_trichotomy y ρ with h | rfl | h
  · exact (lxt_uni_lt hK hyU hρU ⟨upsPt_inE hyU, upsPt_inE hρU, h, hρ1⟩ huy hty).1 hlt
  · exact hlt
  · exact (lxt_uni_lt hK hρU hyU ⟨upsPt_inE hρU, upsPt_inE hyU, h, hy1⟩ hu ht).2 hlt

/-- **The Cantor normal form of a code `g < ω^U` (`U ≤ ε_{c+1}`) as an exponent list of `LxTm K`.** -/
theorem lxCNF (hK : LxEK K) (M : XtLay) {c Z ρ : Ordinal.{0}} (hZ : SC Z)
    (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y c) (hP : LgPoly K.sys c) (hρU : UpsPt ρ) (hρS : SC ρ)
    (hρ1 : ρ < Om 1) (hZρ : Z ≤ ρ) :
    ∀ g, LgCl Z g → ∀ U, U ≤ eN c → g < ω ^ U →
      ∃ ps : List (LxTm K × Ordinal.{0}), ps.Pairwise LxGt ∧
        (∀ q ∈ ps, (∃ d, LgCl Z d ∧ d < U ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → q.1.CBt y ∧ q.1.val y = lgTh y d) ∧
          0 < q.2 ∧ q.2 < ω) ∧
        ∀ y, SC y → y < Om 1 → Z ≤ y → lxSum M y ps = ω ^ M.E y * lgTh y g := by
  have hρ1' : ρ < Om1 := by rw [ph_Om1_eq]; exact hρ1
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg U hU hgU
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨[], List.Pairwise.nil, fun q hq => absurd hq List.not_mem_nil, fun y _ _ _ => by
      rw [lgTh_zero, mul_zero]; rfl⟩
  obtain ⟨hsub, hlog⟩ := lgDec hZ g hg
  set Lg := log ω g with hLdef
  have hLU : Lg < U := (lt_opow_iff_log_lt one_lt_omega0 hg0).1 hgU
  have hT0 : ω ^ Lg ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hk : g / ω ^ Lg < ω := by
    refine (Ordinal.lt_mul_iff_div_lt hT0).1 ?_
    have := lt_opow_succ_log_self one_lt_omega0 g
    rwa [opow_succ] at this
  obtain ⟨n, hn⟩ := lt_omega0.1 hk
  have hn0 : 0 < n := by
    have h1 : (1 : Ordinal.{0}) ≤ g / ω ^ Lg :=
      (Ordinal.mul_le_iff_le_div hT0).1 (by rw [mul_one]; exact opow_log_le_self ω hg0)
    rw [hn] at h1; exact_mod_cast h1
  have hgdec : ω ^ Lg * n + g % ω ^ Lg = g := by rw [← hn]; exact div_add_mod g _
  have hwn : LgCl Z (ω ^ Lg * n) := LgCl.mul_nat hZ.1 (LgCl.opow hZ.1 hlog) n
  have hr : LgCl Z (g % ω ^ Lg) := by
    have := hsub _ hwn (by rw [← hgdec]; exact le_self_add)
    rwa [Ordinal.sub_eq_of_add_eq hgdec] at this
  have hrL : g % ω ^ Lg < ω ^ Lg := mod_lt g hT0
  have hrg : g % ω ^ Lg < g := hrL.trans_le (opow_log_le_self ω hg0)
  obtain ⟨ps, hpw, hps, hsum⟩ := IH _ hrg hr Lg (hLU.le.trans hU) hrL
  obtain ⟨t, ht⟩ := lxExpTm hZ hE hP Lg hlog (hLU.trans_le hU)
  obtain ⟨htρ, htv⟩ := ht ρ hρS hρ1 hZρ
  refine ⟨(t, (n : Ordinal.{0})) :: ps, List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩, fun q hq => ?_,
    fun y hy hy1 hZy => ?_⟩
  · obtain ⟨⟨d, hd, hdL, hdv⟩, -⟩ := hps q hq
    obtain ⟨hqρ, hqv⟩ := hdv ρ hρS hρ1 hZρ
    refine lxGt_of_ref hK hρU hρ1' htρ hqρ ?_
    rw [hqv, htv]; exact lgTh_lt (hd.mono hZρ) hdL
  · rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨⟨Lg, hlog, hLU, ht⟩, show (0 : Ordinal.{0}) < (n : Ordinal.{0}) by exact_mod_cast hn0,
        natCast_lt_omega0 n⟩
    · obtain ⟨⟨d, hd, hdL, hdv⟩, h2⟩ := hps q hq'
      exact ⟨⟨d, hd, hdL.trans hLU, hdv⟩, h2⟩
  · obtain ⟨-, htv'⟩ := ht y hy hy1 hZy
    have hly := hlog.mono hZy
    have hny : LgCl y (n : Ordinal.{0}) := LgCl.small (lx_nat_lt (gg_SC_eps hy) n)
    rw [lxSum_cons, hsum y hy hy1 hZy]
    show ω ^ (M.E y + t.val y) * (n : Ordinal.{0}) + ω ^ M.E y * lgTh y (g % ω ^ Lg) = ω ^ M.E y * lgTh y g
    conv_rhs => rw [← hgdec]
    rw [lgTh_add hy (hwn.mono hZy), lgTh_opow_mul hy hly _ hny,
      lgTh_small (lx_nat_lt (gg_SC_eps hy) n).le, htv', mul_add, opow_add, mul_assoc]

end Codes

/-! ## THE GENERIC STEP ON CODES -/

/-- **The generic step on codes**: `lxNext K` has terms for every code below `ε_{c+1}`. -/
theorem lxNextPoly (K : XtLay) (hK : LxEK K) (hpi : LxEpPi K) {c : Ordinal.{0}} (hc : ∀ Z, SC Z → LgCl Z c)
    (hcE : ω ^ c = c) (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y c) (hP : LgPoly K.sys c) :
    LgPoly (lxNext K hK hpi).sys (eN c) := by
  refine lgPoly_of_SC fun Z hZ hZ1 d hd hdE => ?_
  obtain ⟨ρ, hρU, hρS, hρ1, hZρ⟩ := Fp.fpRef hZ1
  obtain ⟨g, r, hg, hr, hre, hdgr⟩ := lgDivCode hZ (hc Z hZ) d hd
  have hrc : r < c := hcE ▸ hre
  have hgE : g < ω ^ eN c := by
    rw [show ω ^ eN c = eN c from eN_E c]
    refine lt_of_le_of_lt ?_ hdE
    calc g ≤ ω ^ c * g := le_mul_right g (opow_pos c omega0_pos)
      _ ≤ d := by rw [hdgr]; exact le_self_add
  obtain ⟨ps, hpw, hps, hsum⟩ := lxCNF hK K hZ hE hP hρU hρS hρ1 hZρ g hg (eN c) le_rfl hgE
  obtain ⟨s, hs⟩ := hP Z r hr hrc
  refine ⟨(ps, s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨hpw, fun q hq => ⟨((hps q hq).1.choose_spec.2.2 y hy hy1 hZy).1, (hps q hq).2⟩, h1⟩, ?_⟩
  show lxVal K (ps, s) y = lgTh y d
  unfold lxVal
  have hgy := hg.mono hZy
  have hcy := hc y hy
  rw [hsum y hy hy1 hZy, show K.sys.val s y = lgTh y r from h2, hdgr,
    lgTh_add hy (lg_cl_opow_mul hy hcy g hgy), lgTh_opow_mul hy hcy g hgy, ← hE y hy hy1]

/-- The top of `lxNext K`: `ε_{E_K(y)+1} = Θ'_y(ε_{c+1})`. -/
theorem lxNextTop (K : XtLay) (hK : LxEK K) (hpi : LxEpPi K) {c : Ordinal.{0}} (hc : ∀ Z, SC Z → LgCl Z c)
    (hec : ∀ Z, SC Z → LgCl Z (eN c)) (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y c) :
    ∀ y, SC y → y < Om 1 → (lxNext K hK hpi).sys.top y = lgTh y (eN c) := by
  intro y hy hy1
  show eN (K.E y) = _
  rw [hE y hy hy1, lxTh_eN hy (hc y hy) (hec y hy)]

/-! ## The codes `ε_{Γ_{Ω₁+1}+n}` -/

/-- **The code `ε_{Γ_{Ω₁+1}+n}`** (`= veblen 1 (Γ_{Ω₁+1} + n)`). -/
noncomputable def lxC (n : ℕ) : Ordinal.{0} := veblen 1 (ggGam + n)

theorem lxC_zero : lxC 0 = ggGam := by
  unfold lxC; rw [Nat.cast_zero, add_zero]
  exact ggGam_spec.1.veblen_right (gg_one_lt_of_SC ggGam_spec.1)

theorem lxC_succ (n : ℕ) : lxC (n + 1) = eN (lxC n) := by
  unfold lxC eN
  rw [Nat.cast_succ, ← add_assoc, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact epsilon_succ_eq_nfp _

theorem lx_cl_C (n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (lxC n) :=
  LgCl.phi (LgCl.small (gg_one_lt_of_SC hZ)) (LgCl.add LgCl.gam (LgCl.small (lx_nat_lt (gg_SC_eps hZ) n)))

theorem lxC_eps (n : ℕ) : ω ^ lxC n = lxC n := gg_veblen_eps one_ne_zero

theorem lx_y1 {y : Ordinal.{0}} (hy1 : y < Om 1) : y < Om1 := by rw [ph_Om1_eq]; exact hy1

/-- **`Θ'_y(ε_{Γ_{Ω₁+1}+n}) = lxG n y`** (`= ε_{Γ(y)+n}`). -/
theorem lxTh_C {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ∀ n : ℕ, lgTh y (lxC n) = lxG n y
  | 0 => by rw [lxC_zero, lgTh_Gam hy hy1]; rfl
  | n + 1 => by
    rw [lxC_succ, lxTh_eN hy (lx_cl_C n hy) (by rw [← lxC_succ]; exact lx_cl_C (n + 1) hy), lxTh_C hy hy1 n,
      lxG_succ (gg_SC_eps hy) (lx_y1 hy1)]

theorem lx_Om1_le_C (n : ℕ) : Om 1 ≤ lxC n :=
  ggGam_spec.2.le.trans (le_self_add.trans (right_le_veblen _ _))

theorem lxC_le_Gam' (S : InaccSeq.{0}) (n : ℕ) : lxC n ≤ lgGam' := (lgCl_lt_Gam' S (lx_cl_C n ph_SC_Om1)).le

/-! ## The layers `K_n` -/

/-- A layer with `E(x) = lxG n x`. -/
abbrev LxKs (n : ℕ) := {K : XtLay // ∀ x, InE x → x < Om1 → K.E x = lxG n x}

theorem lxKs_EK {n : ℕ} (K : LxKs n) : LxEK K.1 := fun x hx hx1 => by
  rw [K.2 x hx hx1]; exact lxG_inE hx hx1 n

theorem lxKs_pi {n : ℕ} (K : LxKs n) : LxEpPi K.1 := fun σ ρ hσ _ hB => by
  rw [K.2 ρ hB.2.1 hB.2.2.2, K.2 σ hB.1 (hB.2.2.1.trans hB.2.2.2)]
  exact lxG_eN_pi hσ hB n

/-- The step on the layers with `E = lxG n`. -/
noncomputable def lxKsucc {n : ℕ} (K : LxKs n) : LxKs (n + 1) :=
  ⟨lxNext K.1 (lxKs_EK K) (lxKs_pi K), fun x hx hx1 => by
    rw [lxNext_E, K.2 x hx hx1, lxG_succ hx hx1]⟩

/-- The layers with the invariant `E = lxG n`. -/
noncomputable def lxKp : (n : ℕ) → LxKs n
  | 0 => ⟨lgLay, fun _ _ _ => rfl⟩
  | n + 1 => lxKsucc (lxKp n)

/-- **The `n`-th layer**: `lxK 0 = lgLay` (top `Γ(x)`), `lxK (n+1) = lxNext (lxK n)` (top `ε_{Γ(x)+n+1}`). -/
noncomputable def lxK (n : ℕ) : XtLay := (lxKp n).1

theorem lxK_zero : lxK 0 = lgLay := rfl

theorem lxK_succ (n : ℕ) : lxK (n + 1) = lxNext (lxK n) (lxKs_EK (lxKp n)) (lxKs_pi (lxKp n)) := rfl

theorem lxK_E (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (lxK n).E x = lxG n x :=
  (lxKp n).2 x hx hx1

theorem lxK_EK (n : ℕ) : LxEK (lxK n) := lxKs_EK (lxKp n)

theorem lxK_top (n : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (lxK n).sys.top x = lxG n x := by
  rw [lx_top (lxK_EK n) hx hx1, lxK_E n hx hx1]

theorem lxK_Eth (n : ℕ) : ∀ y, SC y → y < Om 1 → (lxK n).E y = lgTh y (lxC n) := fun y hy hy1 => by
  rw [lxK_E n (gg_SC_eps hy) (lx_y1 hy1), lxTh_C hy hy1]

/-- **`LgPoly (lxK n) (ε_{Γ_{Ω₁+1}+n})`, top `Θ'` of it.** -/
theorem lxK_poly : ∀ n : ℕ, LgPoly (lxK n).sys (lxC n) ∧
    ∀ y, SC y → y < Om 1 → (lxK n).sys.top y = lgTh y (lxC n)
  | 0 => by
    refine ⟨?_, fun y hy hy1 => ?_⟩
    · rw [lxC_zero]; have h := lqLay_poly; rwa [lg_Gam_eps] at h
    · rw [lxK_top 0 (gg_SC_eps hy) (lx_y1 hy1), lxTh_C hy hy1]
  | n + 1 => by
    refine ⟨?_, fun y hy hy1 => ?_⟩
    · rw [lxK_succ, lxC_succ]
      exact lxNextPoly (lxK n) _ _ (fun _ hZ => lx_cl_C n hZ) (lxC_eps n) (lxK_Eth n) (lxK_poly n).1
    · rw [lxK_top (n + 1) (gg_SC_eps hy) (lx_y1 hy1), lxTh_C hy hy1]

theorem lxG_ge_G {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ∀ n : ℕ, lgG x ≤ lxG n x
  | 0 => le_rfl
  | n + 1 => by rw [lxG_succ hx hx1]; exact (lxG_ge_G hx hx1 n).trans (lt_eN _).le

theorem lxK_topE (n : ℕ) (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < (lxK n).sys.top x := by
  rw [lxK_top n hx hx1]
  exact ((eN_le_gT hx hx1 0).trans_lt (gT_lt_lgG hx hx1 0)).trans_le (lxG_ge_G hx hx1 n)

variable {S : InaccSeq.{0}}

/-- **`Λ⁺(lxK n) = ι(ε_{Γ_{Ω₁+1}+n}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lxK_loc (n : ℕ) : xtB1 (lxK n).sys = iota S (lxC n * ω) ∧
    upsilon (xtB1 (lxK n).sys) = Pv S (lxC n * ω) ∧ Pv S (lxC n * ω) < Nc.ncL S 0 := by
  have h := lgB1_eq2 (S := S) (lxC_le_Gam' S n) (lxK_poly n).1 (lxK_poly n).2 (fun _ hZ => lx_cl_C n hZ)
    (lx_Om1_le_C n) (lxK_topE n) (lxK n).topPkg
  rwa [lxC_eps n] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lxK n)`.** -/
theorem lxKT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lxK n).sys)
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lxK n).sys l := by
  have hlt : l < iota S (ω ^ lxC n * ω) := by rw [lxC_eps n, ← (lxK_loc (S := S) n).1]; exact hlB
  exact lgUniTh (lxC_le_Gam' S n) (lxK_poly n).1 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem lxK_nonfix (n : ℕ) : XtNonfix (xtOrec (lxK n).sys) (xtB1 (lxK n).sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lxK n).topPkg))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lxK n)`**, fixed points of `υ` included. -/
theorem lxKEnum (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lxK n).sys) :
    CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (lxK n).topPkg) (lxK_nonfix n) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (lxK n).topPkg) hr.1 hl).2 (lxKT_fix n hr hl hfx.symm)

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lxK n)`.** -/
theorem lxK_capV (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (lxK n).sys)
    (hfix : l < upsilon l) : CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 (lxK n).topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (lxK_nonfix n l hr.1 hww hfix hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(lxK n)}`** in `R₂^C`, with the exact reaches `lh(ρ_λ) = δ_λ + O_{lxK n}(λ)`. -/
theorem lxK_blk (n : ℕ) :
    (∀ c d, c < d → d < upsilon (xtB1 (lxK n).sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (lxK n).sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (lxK n).sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lxK n).sys l)) ∧
    (∀ α < upsilon (xtB1 (lxK n).sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (lxK n).topPkg

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lxK n)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lxKRoad (n : ℕ) (hU : ∀ l, CdRange S l → xtB1 (lxK n).sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 (lxK n).sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 (lxK n).sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 (lxK n).topPkg) (lxK_nonfix n) hU hL (fun _ hr hlB hfix => lxKT_fix n hr hlB hfix) hV hC hEQ
    hrest hB2

/-! ## The chain and its supremum `ι(ε_{Γ_{Ω₁+1}+ω})` -/

theorem lxK_topIn (n : ℕ) : LyTopIn (lxK (n + 1)).sys (lxK n).sys :=
  lxEp_topIn (lxK n) (lxK n) (lxK_EK n) (fun _ _ _ => le_rfl) (fun _ _ _ => lt_eN _)

/-- `Λ⁺(lxK n)`. -/
noncomputable def lxLam (n : ℕ) : Ordinal.{0} := xtB1 (lxK n).sys

theorem lxLam_lt (n : ℕ) : lxLam n < lxLam (n + 1) :=
  lyB1_lt (lxK (n + 1)).topPkg (lxK n).topPkg (lxK_topIn n)

theorem lxLam_strictMono : StrictMono lxLam := strictMono_nat_of_lt_succ lxLam_lt

/-- `O_{lxK m} = O_{lxK n}` below `Λ⁺(lxK n)` for `n ≤ m`. -/
theorem lxK_eq {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < lxLam n) :
    xtOrec (lxK m).sys μ = xtOrec (lxK n).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact lyEq (lxK m).topPkg (lxK_topIn m) hμ (hμn.trans_le (lxLam_strictMono.monotone hnm))

/-- **The family of the layers `lxK n`**: bounds `Λ⁺(lxK n)`, offsets `O_{lxK n}`. -/
noncomputable def lxFam : XtFam where
  bd := lxLam
  off := fun n => xtOrec (lxK n).sys
  spec := fun n => xtSpec1 (lxK n).topPkg
  mono := lxLam_lt
  nonfix := lxK_nonfix

/-- **ENUM-REACH at every restart of the range below `sup_n Λ⁺(lxK n)`**, fixed points of `υ` included. -/
theorem lxFamEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lxFam.famSup) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, hn⟩ := lxFam.famLt hl
  exact lxKEnum n hr hn

/-- **The cap of the values at every non-fixed restart of the range below `sup_n Λ⁺(lxK n)`.** -/
theorem lxFam_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lxFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lxFam.famCapV hr hl hfix

/-- **Theorem BLK^O below `υ_{sup_n Λ⁺(lxK n)}`** in `R₂^C`. -/
theorem lxFam_blk :
    (∀ c d, c < d → d < upsilon lxFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lxFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lxLam k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lxK k).sys l)) ∧
    (∀ α < upsilon lxFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lxFam.famBlk

/-- **The road with UPPER and LOWER asked only at `λ ≥ sup_n Λ⁺(lxK n)`**: the rest is CapV at the outer restarts
below `L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lxFamRoad (hU : ∀ l, CdRange S l → lxFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lxFam.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lxFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lxFam.famRoad3 hU hL (fun n _ hr hln hfix => lxKT_fix n hr hln hfix) hV hC hEQ hrest hB2

/-- **The code `ε_{Γ_{Ω₁+1}+ω}`** of the supremum. -/
noncomputable def lxCw : Ordinal.{0} := veblen 1 (ggGam + ω)

theorem lx_cl_Cw {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z lxCw :=
  LgCl.phi (LgCl.small (gg_one_lt_of_SC hZ)) (LgCl.add LgCl.gam (LgCl.small (omega0_lt_inE (gg_SC_eps hZ))))

theorem lxC_lt_Cw (n : ℕ) : lxC n < lxCw :=
  veblen_lt_veblen_iff_right.2 ((add_lt_add_iff_left _).2 (natCast_lt_omega0 n))

theorem lxLam_loc (n : ℕ) : lxLam n = iota S (lxC n * ω) := (lxK_loc n).1

/-- **`sup_n Λ⁺(lxK n) = ι(ε_{Γ_{Ω₁+1}+ω})`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lxFam_loc : lxFam.famSup = iota S lxCw ∧
    upsilon lxFam.famSup = Pv S lxCw ∧ Pv S lxCw < Nc.ncL S 0 := by
  have hEw : ω ^ lxCw = lxCw := gg_veblen_eps one_ne_zero
  have hwC : ω < lxCw := omega0_lt_inE hEw
  have hstep : ∀ n : ℕ, lxC n * ω < lxCw := fun n => InE.mul_lt hEw (lxC_lt_Cw n) hwC
  have hlim : IsSuccLimit lxCw := by
    have := ph_opow_lim (c := lxCw) (lt_of_le_of_lt zero_le hwC).ne'
    rwa [hEw] at this
  have heq : lxFam.famSup = iota S lxCw := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lxLam n ≤ _
      rw [lxLam_loc (S := S) n]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      have he : e.1 < veblen 1 (ggGam + ω) := e.2
      obtain ⟨a, ha, hea⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add ggGam isSuccLimit_omega0)).1 he
      have hn : ∃ n : ℕ, a < ggGam + n := by
        rcases lt_or_ge a ggGam with h | h
        · exact ⟨0, by rw [Nat.cast_zero, add_zero]; exact h⟩
        · obtain ⟨t, rfl⟩ := exists_add_of_le h
          have ht : t < ω := (add_lt_add_iff_left _).1 ha
          obtain ⟨m, rfl⟩ := lt_omega0.1 ht
          exact ⟨m + 1, (add_lt_add_iff_left _).2 (by exact_mod_cast Nat.lt_succ_self m)⟩
      obtain ⟨n, hn⟩ := hn
      have h1 : e.1 < lxC n * ω := by
        refine hea.trans ((veblen_lt_veblen_iff_right.2 hn).trans_le ?_)
        exact le_mul_of_one_le_right zero_le one_lt_omega0.le
      calc iota S e.1 ≤ iota S (lxC n * ω) := iota_mono _ _ h1.le
        _ = lxLam n := (lxLam_loc n).symm
        _ ≤ lxFam.famSup := (lxFam.famBd_lt n).le
  have hups : upsilon lxFam.famSup = Pv S lxCw := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ?_⟩
  rw [← hups]
  have := (lgIota_lt_L0 (S := S) (fun Z hZ => lx_cl_Cw hZ)).2
  rwa [← heq] at this

/-- **Where the supremum lies**: `ρ(Λ⁺(lxK n)) < ρ(sup_n Λ⁺(lxK n)) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and
`sup_n Λ⁺(lxK n) < L(ω+1)`, unconditionally. -/
theorem lxFam_fr_order (n k : ℕ) :
    upsilon (lxLam n) < upsilon lxFam.famSup ∧ upsilon lxFam.famSup < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    lxFam.famSup < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lxFam_loc (S := S)
  have hU : upsilon lxFam.famSup < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono (lxFam.famBd_lt n), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

/-- **The previous frontier lies below `Λ⁺(lxK 1)`**: `sup_n Λ⁺(lqBN n) = ι(ω^{ω^{Γ_{Ω₁+1}+phB·ω}}) <
ι(ε_{Γ_{Ω₁+1}+1}·ω) = Λ⁺(lxK 1)`. -/
theorem lxBN_lt_K1 (S : InaccSeq.{0}) : lqFamB.famSup < lxLam 1 := by
  rw [(lqFamB_loc (S := S)).1, lxLam_loc (S := S) 1]
  have hE1 : ω ^ lxC 1 = lxC 1 := lxC_eps 1
  have hG1 : ggGam < lxC 1 := by rw [lxC_succ, lxC_zero]; exact lt_eN _
  have hw : lqBNw < lxC 1 := by
    unfold lqBNw
    have hBw : phB * ω < ggGam := by
      have hGE : ω ^ ggGam = ggGam := lg_Gam_eps
      exact InE.mul_lt hGE lq_B_lt_Gam (omega0_lt_inE hGE)
    have hGG : ggGam + phB * ω < ggGam + ggGam := (add_lt_add_iff_left _).2 hBw
    exact hGG.trans ((inE_indec hE1).add_lt hG1 hG1)
  have h1 : ω ^ ω ^ lqBNw < lxC 1 := by
    rw [← hE1]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rw [← hE1]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 hw
  have h2 : ω ^ ω ^ lqBNw < lxC 1 * ω := h1.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
  exact cd_iota_lt_of_good (lg_good (fun Z hZ => lq_cl_BNw hZ)) h2

end Googology.Trans.PoR.InaccPsi.R2.Lx
