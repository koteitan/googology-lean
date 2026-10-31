import Googology.Trans.PoR.InaccPsi.R2.HoBand

/-!
# HoBR: OVER A BASE DATUM `D`, ONE RECURSION OF SYSTEMS AT `φ(Ω₁²·v + Ω₁·μ, F+1)`, `μ < Ω₁`, AND THEIR UNION

ONE generic form of `Hn.HnQG` + `Hn.HnQU` (over a pseudo-base, members `Hl.hlkPk μ`) and `Hn.HnG` + `Hn.HnU` (over `G`,
members `Hn.hnkPk μ`): for every prefix `Ω₁²·v` (`1 ≤ v < Ω₁`), every band family `Kf : HoBF v` and every base datum
`D : HoWD v` (`G`, or a pseudo-base of the next prefix), started at a start `S₀` over `hoW D (Kf.K 0)`:

* `hoRGS μ` (successor: the union `Hn.hnwU` over `hoW D (Kf.K μ)` with the steps of `Kf.K μ`; limit: the gated
  `ω`-chain at `heFs λ k`), `hoRGS_inv` (**a start over `hoW D (Kf.K μ)` with base gate `max γ g_μ`, extending all
  earlier members**), `hoRGS_B` (`φ(Ω₁²·v + Ω₁·μ, F+1)`);
* `hoR_small` (**SMALL**), `hoR_high` (codes past `S₀` with gate below `σ` force `hlGt v < σ`);
* `hoRFam` (**the family as an `Ho.HoFam`**: union bound `hdNx (Ω₁²·(v+1)) F`, gate `max γ (hlGt (v+1))`, base reading
  `hdNx (x·x·(v+1)) (F(x))`), `hoRU` (**THE UNION**).

What differs from the four `Hn` modules: the prefix `Ω₁²·v` as a parameter, the members and the base as data, the
outer low field `D.Zo`, the gate `max γ (hlGt (v+1))` of the union.  No new axiom.  New definitions: `HoRCoh`, `hoRCh`,
`hoRLimF`, `hoRSucc`, `hoRGS`, `hoRFam`, `hoRU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Level arithmetic -/

section Arith

variable {v : Ordinal.{0}} (hv1 : 1 ≤ v)

theorem hoL_lt_next {a M : Ordinal.{0}} (ha : InE a) (hM : M < a) : a * a * v + a * M < a * a * (v + 1) :=
  (le_self_add.trans le_self_add).trans_lt (ho_band_lt ha hM)

theorem hoL_succ_lt_next {a M : Ordinal.{0}} (ha : InE a) (hM : M < a) : a * a * v + a * M + 1 < a * a * (v + 1) :=
  (add_le_add le_self_add le_rfl).trans_lt (ho_band_lt ha hM)

include hv1 in
theorem hoL_one {a M : Ordinal.{0}} (ha : InE a) : (1 : Ordinal.{0}) < a * a * v + a * M :=
  ((one_lt_omega0.trans (omega0_lt_inE ha)).trans_le ((le_mul_of_one_le_right'
    (one_lt_omega0.trans (omega0_lt_inE ha)).le).trans (ho_xsq_le hv1))).trans_le le_self_add

include hv1 in
theorem hoL_ne {a M : Ordinal.{0}} (ha : InE a) : a * a * v + a * M ≠ 0 := (zero_lt_one.trans (hoL_one hv1 ha)).ne'

theorem ho_next_ne {a : Ordinal.{0}} (ha : InE a) : a * a * (v + 1) ≠ 0 :=
  (mul_pos (mul_pos ha.pos ha.pos) (Order.lt_add_one_iff.2 zero_le)).ne'

theorem ho_two_lt_next {a : Ordinal.{0}} (ha : InE a) : (2 : Ordinal.{0}) < a * a * (v + 1) :=
  ((show (2 : Ordinal.{0}) < ω from by exact_mod_cast natCast_lt_omega0 2).trans ((omega0_lt_inE ha).trans
    (hl_lt_sq ha))).trans_le (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (Order.lt_add_one_iff.2 zero_le)))

theorem ho_x_lt_next {a : Ordinal.{0}} (ha : InE a) : a < a * a * (v + 1) :=
  (hl_lt_sq ha).trans_le (le_mul_of_one_le_right' (Order.one_le_iff_pos.2 (Order.lt_add_one_iff.2 zero_le)))

/-- **Cofinality of the band levels in the next prefix**: `b < A + a·a` (`A` closed under successor) gives
`b + 1 < A + a·μ` for some `μ < a`. -/
theorem ho_cof_band {a A b : Ordinal.{0}} (ha : InE a) (hA : ∀ b, b < A → b + 1 < A) (hb : b < A + a * a) :
    ∃ μ, μ < a ∧ b + 1 < A + a * μ := by
  have hlx := ev_isSuccLimit_of_inE ha
  rcases lt_or_ge b A with h | h
  · exact ⟨0, ha.pos, by rw [mul_zero, add_zero]; exact hA b h⟩
  · obtain ⟨b', rfl⟩ := exists_add_of_le h
    have hb' : b' < a * a := (add_lt_add_iff_left _).1 hb
    have hdiv : b' / a < a := (lt_mul_iff_div_lt ha.pos.ne').1 hb'
    refine ⟨b' / a + 1 + 1, hlx.add_one_lt (hlx.add_one_lt hdiv), ?_⟩
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    calc b' + 1 ≤ a * (b' / a) + a := Order.add_one_le_of_lt (lt_mul_div_add b' ha.pos.ne')
    _ = a * (b' / a + 1) := by rw [mul_add_one]
    _ < a * (b' / a + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) ha.pos

theorem ho_hv' {v x γ : Ordinal.{0}} (h : max γ (hlGt (v + 1)) < x) : hlGt v < x :=
  (ho_hlGt_le_succ v).trans_lt (max_lt_iff.1 h).2

end Arith

section BR

variable {v : Ordinal.{0}} {hv1 : 1 ≤ v} {hv : v < Om1} (Kf : HoBF v hv1 hv) (D : HoWD v)

theorem hoD_Ffix {M : Ordinal.{0}} (hM : M < Om1) : veblen (Om1 * Om1 * v + Om1 * M) D.F = D.F :=
  D.F_fix _ (hoL_lt_next gl_Om1_E hM)

theorem hoD_B_eq {M : Ordinal.{0}} (hM : M < Om1) :
    veblen (Om1 * Om1 * v + Om1 * M) (D.F + 1) = hdNx (Om1 * Om1 * v + Om1 * M) D.F :=
  (hdNx_fixP (hoD_Ffix D hM)).symm

section Base

variable {M x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : D.γ < x) (hvx : hlGt v < x) (hMx : M < x)
include hx hx1 hγ hvx hMx

theorem hoD_Frfix : veblen (x * x * v + x * M) (D.Fr x) = D.Fr x :=
  D.Fr_fix hx hx1 hγ hvx _ (hoL_lt_next hx hMx)

theorem hoD_b_eq : veblen (x * x * v + x * M) (D.Fr x + 1) = hdNx (x * x * v + x * M) (D.Fr x) :=
  (hdNx_fixP (hoD_Frfix D hx hx1 hγ hvx hMx)).symm

theorem hoD_b_lt : hdNx (x * x * v + x * M) (D.Fr x) < hdNx (x * x * (v + 1)) (D.Fr x) :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (hoL_succ_lt_next hx hMx))

end Base

/-- **Lemma EXACT for `hdNx (ℓ(ρ)+0) (F(ρ))`** at a level below the next prefix, above both gates. -/
theorem hoD_N0_pi (Λ : HnLv) (h : HoGood v Λ) {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : D.γ < σ) (hg : Λ.g < σ) :
    hdNx (Λ.l ρ + 0) (D.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (Λ.l ρ + 0) (D.Fr ρ)) = hdNx (Λ.l σ + 0) (D.Fr σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : D.γ < ρ := hγ.trans hB.2.2.1
  have hgρ : Λ.g < ρ := hg.trans hB.2.2.1
  have hfix : ∀ {y}, InE y → y < Om1 → D.γ < y → Λ.g < y → veblen (Λ.l y + 0) (D.Fr y) = D.Fr y :=
    fun {y} hy hy1 hγy hgy => hc_fix_down (by rw [add_zero]; exact le_self_add) (D.rfix h hy hy1 hγy hgy)
  have hgt : ∀ {y}, InE y → y < Om1 → D.γ < y → Λ.g < y → Λ.l y + 0 < D.Fr y :=
    fun {y} hy hy1 hγy hgy => (by rw [add_zero]; exact le_self_add : Λ.l y + 0 ≤ Λ.l y + y).trans_lt
      (D.rgt h hy hy1 hγy hgy)
  obtain ⟨f1, f2⟩ := D.Fr_pi hB hγ
  have hh := hnv_glA_pi Λ hB hg hB.1.pos f1 (D.rlt1 h hB.2.1 hρ1 hγρ hgρ)
  rw [f2, hnv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (hfix hB.2.1 hρ1 hγρ hgρ) (hgt hB.2.1 hρ1 hγρ hgρ)
    (D.rlt1 h hB.2.1 hρ1 hγρ hgρ), hnv_glA_fixP Λ hB.1 hσ1 hB.1.pos (hfix hB.1 hσ1 hγ hg) (hgt hB.1 hσ1 hγ hg)
    (D.rlt1 h hB.1 hσ1 hγ hg)] at hh
  exact hh

theorem ho_next_E : InE (hdNx (Om1 * Om1 * (v + 1)) D.F) := hdNx_E (ho_next_ne gl_Om1_E) _

/-! ## The limit case -/

/-- **The condition at a limit**: the earlier systems are starts over `hoW D (Kf.K μ)` with base gate
`max γ g_μ`, and later ones extend earlier ones. -/
def HoRCoh (l : Ordinal.{0}) (IH : ∀ μ, μ < l → HgVD) : Prop :=
  (∀ μ (h : μ < l) (hμ : μ < Om1), HnWShape (hoW D (Kf.K μ).Λ (Kf.good hμ)) 0 (IH μ h) ∧
      (IH μ h).γ = max D.γ (Kf.K μ).Λ.g) ∧
    ∀ μ' μ (h' : μ' < l) (h : μ < l), μ' < μ → ∀ c x, c < (IH μ' h').B →
      (IH μ h).R c x = (IH μ' h').R c x ∧ (IH μ h).g c = (IH μ' h').g c

section Lim

variable (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ μ, μ < l → HgVD) (H : HoRCoh Kf D l IH)

include hl hle in
theorem hoRCoh_g (k : ℕ) : (Kf.K (heFs l k)).Λ.g ≤ max (hlGt v) (hlGt l) :=
  (Kf.ghi _ ((heFs_lt hl (hl_om hle) k).trans hle)).trans (max_le_max le_rfl (hlGt_mono (heFs_lt hl (hl_om hle) k).le))

include H in
theorem hoRCoh_B (k : ℕ) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).B = veblen (Om1 * Om1 * v + Om1 * heFs l k) (D.F + 1) := by
  have hk1 := (heFs_lt hl (hl_om hle) k).trans hle
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k) hk1).1.1
  rw [h]
  show veblen ((Kf.K (heFs l k)).Λ.L + 0) (D.F + 1) = _
  rw [Kf.L _ hk1, add_zero]

include H in
theorem hoRCoh_b (k : ℕ) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
    (hγ : max D.γ (max (hlGt v) (hlGt l)) < x) :
    (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).b x = veblen (x * x * v + x * heFs l k) (D.Fr x + 1) := by
  have hk1 := (heFs_lt hl (hl_om hle) k).trans hle
  have hg' := (hoRCoh_g Kf l hl hle k).trans_lt (max_lt_iff.1 hγ).2
  have h := (H.1 _ (heFs_lt hl (hl_om hle) k) hk1).1.2.2.1 x hx hx1 (max_lt (max_lt (max_lt_iff.1 hγ).1 hg') hx.pos)
  rw [h]
  show veblen ((Kf.K (heFs l k)).Λ.l x + 0) (D.Fr x + 1) = _
  rw [Kf.l _ hk1 x hg', add_zero]

/-- **THE GATED `ω`-CHAIN OF THE SYSTEMS `IH (heFs λ k)` OVER `D`**: union bound `φ(Ω₁²·v + Ω₁·λ, F+1)`, union base
reading `φ(x·x·v + x·λ, F(x)+1)`, union base gate `max γ (max (hlGt v) (hlGt λ))`. -/
noncomputable def hoRCh : HgfCh where
  D := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  B := veblen (Om1 * Om1 * v + Om1 * l) (D.F + 1)
  b := fun x => veblen (x * x * v + x * l) (D.Fr x + 1)
  γ := max D.γ (max (hlGt v) (hlGt l))
  Zo := (hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo
  γ_lt := max_lt D.γ_lt (hoLv v l hv1 hv hle).g_lt
  γ0 := fun k => by
    rw [(H.1 _ _ ((heFs_lt hl (hl_om hle) k).trans hle)).2]
    exact max_le_max le_rfl (hoRCoh_g Kf l hl hle k)
  γ_cl := fun Z hZ hZ1 h => by
    have ha : (1 : Ordinal.{0}) ≤ Om1 * Om1 * v + Om1 * l := (hoL_one hv1 gl_Om1_E).le
    have hG : gcG 0 < veblen (Om1 * Om1 * v + Om1 * l) (D.F + 1) :=
      D.G_le.trans_lt ((lt_add_one _).trans_le (right_le_veblen _ _))
    have hc := hi_cl_lvl ha hZ1 (hd_succ_lt (hoL_ne hv1 gl_Om1_E) _) hG h le_rfl
      ((isNormal_veblen _).strictMono (lt_add_one _))
    have h2 := (hoLv v l hv1 hv hle).L_add_lt (ν := 0) (by rw [← Br.Om1_eq]; exact gv_Om1_pos)
    rw [add_zero] at h2
    refine max_lt ?_ ((hoLv v l hv1 hv hle).g_cl Z _ hZ hZ1 hc le_rfl h2)
    refine D.F_cl Z hZ hZ1 _ h ((lt_add_one _).le.trans (right_le_veblen _ _)) ?_
    rw [hoD_B_eq D hle]
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (hoL_succ_lt_next gl_Om1_E hle))
  B_mono := fun k => by
    rw [hoRCoh_B Kf D l hl hle IH H, hoRCoh_B Kf D l hl hle IH H]
    exact (hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_mono hl (hl_om hle) k) gv_Om1_pos)) _).le
  B_lt := fun k => by
    rw [hoRCoh_B Kf D l hl hle IH H]
    exact hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_lt hl (hl_om hle) k) gv_Om1_pos)) _
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hoL_ne hv1 gl_Om1_E) (hoD_Ffix D hle) hc
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => ho_sqv_succ gl_Om1_lim hv1 h) gv_Om1_pos (heFs_mono hl (hl_om hle))
      (heFs_cof hl (hl_om hle)) hb
    refine ⟨k, ?_⟩
    rw [hoRCoh_B Kf D l hl hle IH H, hoD_B_eq D ((heFs_lt hl (hl_om hle) k).trans hle)]
    exact hcb.trans (hdN_lt_Nx hk)
  R_ext := fun k c x hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c x hc).1
  g_ext := fun k c hc => (H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k) c 0 hc).2
  B_lt1 := by
    rw [hoD_B_eq D hle]
    exact (hdNx_mono (hoL_lt_next gl_Om1_E hle).le _).trans_lt D.S_lt1
  B_fix := veblen_veblen_of_lt (hoL_one hv1 gl_Om1_E) _
  B_mem := fun S a b ha hb =>
    CSet.phi_mem ((hoLv v l hv1 hv hle).L_mem S a b ha (max_lt_iff.1 hb).2)
      (CSet.succ_mem (D.F_mem S ha (max_lt_iff.1 hb).1))
  b_ge := fun k x hx hx1 hγ => by
    rw [hoRCoh_b Kf D l hl hle IH H k hx hx1 hγ]
    exact (hd_veb_left_lt ((add_lt_add_iff_left _).2
      (mul_lt_mul_of_pos_left (heFs_lt hl (hl_om hle) k) hx.pos)) _).le
  b_cof := fun x hx hx1 hγ ν hν => by
    have hlx : l < x := (hoLv_gt hv1 hv hle hx (max_lt_iff.1 hγ).2).2
    have hvx : hlGt v < x := (le_max_left _ _).trans_lt (max_lt_iff.1 hγ).2
    obtain ⟨b, hb, hνb⟩ := hgVeb_cof (hoL_ne hv1 hx) (hoD_Frfix D hx hx1 (max_lt_iff.1 hγ).1 hvx hlx) hν
    obtain ⟨k, hk⟩ := hn_cof1 (fun _ h => ho_sqv_succ (ev_isSuccLimit_of_inE hx) hv1 h) hx.pos
      (heFs_mono hl (hl_om hle)) (heFs_cof hl (hl_om hle)) hb
    refine ⟨k, ?_⟩
    rw [hoRCoh_b Kf D l hl hle IH H k hx hx1 hγ,
      hoD_b_eq D hx hx1 (max_lt_iff.1 hγ).1 hvx ((heFs_lt hl (hl_om hle) k).trans hlx)]
    exact hνb.trans (hdN_lt_Nx hk)
  b_fix := fun x hx _ _ => veblen_veblen_of_lt (hoL_one hv1 hx) _
  b_gt := fun x hx hx1 hγ => ((ho_x_lt_next hx).trans_le (D.Fr_gt hx hx1 (max_lt_iff.1 hγ).1
    ((le_max_left _ _).trans_lt (max_lt_iff.1 hγ).2))).trans ((lt_add_one _).trans_le (right_le_veblen _ _))
  b_lt := fun x hx hx1 hγ => by
    have hlx : l < x := (hoLv_gt hv1 hv hle hx (max_lt_iff.1 hγ).2).2
    have hvx : hlGt v < x := (le_max_left _ _).trans_lt (max_lt_iff.1 hγ).2
    rw [hoD_b_eq D hx hx1 (max_lt_iff.1 hγ).1 hvx hlx]
    exact (hdNx_mono (hoL_lt_next hx hlx).le _).trans_lt ((D.S_Zo hx hx1 (max_lt_iff.1 hγ).1 hvx).trans
      (D.Zo_G1 x hx hx1))
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgσ := (max_lt_iff.1 hγ).2
    have hgρ := hgσ.trans hB.2.2.1
    have hp := hoD_N0_pi D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle) hB (max_lt_iff.1 hγ).1 hgσ
    rw [hoLv_l hv1 hv hle hgρ, hoLv_l hv1 hv hle hgσ, add_zero, add_zero] at hp
    rw [hoD_b_eq D hB.2.1 hρ1 ((max_lt_iff.1 hγ).1.trans hB.2.2.1) ((le_max_left _ _).trans_lt hgρ)
        (hoLv_gt hv1 hv hle hB.2.1 hgρ).2,
      hoD_b_eq D hB.1 hσ1 (max_lt_iff.1 hγ).1 ((le_max_left _ _).trans_lt hgσ) (hoLv_gt hv1 hv hle hB.1 hgσ).2]
    exact hp
  Z_low := fun k x hx hx1 h => by
    have hkl := heFs_lt hl (hl_om hle) k
    have hk1 : heFs l k < Om1 := hkl.trans hle
    show (IH (heFs l k) hkl).Z x ≤ (hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo x
    rw [(H.1 _ _ hk1).1.2.2.2.1 x hx hx1, hoW_Zo_low D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle) h]
    split_ifs with h'
    · have hg' : max D.γ (Kf.K (heFs l k)).Λ.g < x := (max_lt_iff.1 h').1
      have hgk := (max_lt_iff.1 hg').2
      have hvx : hlGt v < x := (Kf.glo _ hk1).trans_lt hgk
      refine (hb_evZ_lt_fix2 (D.Zo_fix x) ?_).le
      show veblen ((Kf.K (heFs l k)).Λ.l x + 0) (D.Fr x + 1) < D.Zo x
      have hfix : veblen ((Kf.K (heFs l k)).Λ.l x + 0) (D.Fr x) = D.Fr x :=
        hc_fix_down (by rw [add_zero]; exact le_self_add) (D.rfix (Kf.good hk1) hx hx1 (max_lt_iff.1 hg').1 hgk)
      rw [← hdNx_fixP hfix]
      refine (hdNx_mono ?_ _).trans_lt (D.S_Zo hx hx1 (max_lt_iff.1 hg').1 hvx)
      rw [add_zero]; exact le_self_add.trans ((Kf.good hk1).2.2 x hx hx1 hgk).le
    · rw [hoW_Zo_low D _ _ (fun h'' => h' (max_lt h'' hx.pos))]
  Zo_fix := fun x => hc_fix_down one_le_two ((hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo_fix x)
  Zo_G1 := fun x hx hx1 => (hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo_G1 x hx hx1

/-- **The union of the chain is a start over `hoW D (Kf.K λ)`.** -/
theorem hoRCh_shape : HnWShape (hoW D (Kf.K l).Λ (Kf.good hle)) 0 (hoRCh Kf D l hl hle IH H).U := by
  refine hoW_congr D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle) (Kf.lim l hl hle).symm (Kf.good hle) ?_
  refine ⟨(by rw [add_zero]; rfl), fun x _ _ => ?_, fun x _ _ hg => ?_, fun x hx _ => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · show max D.γ (max (hlGt v) (hlGt l)) < x ↔ max (max D.γ (max (hlGt v) (hlGt l))) 0 < x
    rw [max_eq_left zero_le]
  · show veblen (x * x * v + x * l) (D.Fr x + 1) = veblen ((hoLv v l hv1 hv hle).l x + 0) (D.Fr x + 1)
    rw [hoLv_l hv1 hv hle (max_lt_iff.1 (max_lt_iff.1 hg).1).2, add_zero]
  · show (if max D.γ (max (hlGt v) (hlGt l)) < x then evZ (veblen (x * x * v + x * l) (D.Fr x + 1))
        else (hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo x) =
      if max (max D.γ (max (hlGt v) (hlGt l))) 0 < x then
        evZ (veblen ((hoLv v l hv1 hv hle).l x + 0) (D.Fr x + 1))
        else (hoW D (hoLv v l hv1 hv hle) (hoLv_good hv1 hv hle)).hnwZo x
    rw [max_eq_left zero_le, add_zero]
    split_ifs with h
    · rw [hoLv_l hv1 hv hle (max_lt_iff.1 h).2]
    · rfl
  · obtain ⟨k, hk⟩ := (hoRCh Kf D l hl hle IH H).B_cof c hc
    rw [(hoRCh Kf D l hl hle IH H).U_g (k := k) hk] at hg
    exact (H.1 _ _ ((heFs_lt hl (hl_om hle) k).trans hle)).1.2.2.2.2 c σ hFc hk hσ hσ1 hg

end Lim

open Classical in
/-- **The limit case**: the union of the chain (when `λ < Ω₁` and the condition holds). -/
noncomputable def hoRLimF (S0 : HgVD) (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ μ, μ < l → HgVD) : HgVD :=
  if h : l < Om1 ∧ HoRCoh Kf D l IH then (hoRCh Kf D l hl h.1 IH h.2).U else S0

open Classical in
/-- **The successor case**: the union over `hoW D (Kf.K μ)` of the levels `Ω₁²·v + Ω₁·μ + κ`, started at `S`. -/
noncomputable def hoRSucc (μ : Ordinal.{0}) (S : HgVD) : HgVD :=
  if hμ : μ < Om1 then
    (if h : HnWShape (hoW D (Kf.K μ).Λ (Kf.good hμ)) 0 S then
      hnwU (hoW D (Kf.K μ).Λ (Kf.good hμ)) (Kf.K μ).St0 (Kf.K μ).h0 S h else S)
  else S

/-- **THE SYSTEMS OVER `D` AT `φ(Ω₁²·v + Ω₁·μ, F+1)`, BY ONE RECURSION ON `μ`**, started at `S₀`. -/
noncomputable def hoRGS (S0 : HgVD) (μ : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) μ S0 (hoRSucc Kf D) (hoRLimF Kf D S0)

variable (S0 : HgVD)

theorem hoRGS_zero : hoRGS Kf D S0 0 = S0 := by unfold hoRGS; rw [Ordinal.limitRecOn_zero]

theorem hoRGS_succ (μ : Ordinal.{0}) : hoRGS Kf D S0 (μ + 1) = hoRSucc Kf D μ (hoRGS Kf D S0 μ) := by
  unfold hoRGS; rw [Ordinal.limitRecOn_add_one]

theorem hoRGS_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    hoRGS Kf D S0 l = hoRLimF Kf D S0 l hl (fun μ _ => hoRGS Kf D S0 μ) := by
  unfold hoRGS; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hoRGS_Bsh {μ : Ordinal.{0}} (hμ : μ < Om1) {S : HgVD} (h : HnWShape (hoW D (Kf.K μ).Λ (Kf.good hμ)) 0 S) :
    S.B = veblen (Om1 * Om1 * v + Om1 * μ) (D.F + 1) := by
  rw [h.1]; show veblen ((Kf.K μ).Λ.L + 0) (D.F + 1) = _; rw [Kf.L μ hμ, add_zero]

theorem hoR_veb_lt {μ' μ : Ordinal.{0}} (h : μ' < μ) :
    veblen (Om1 * Om1 * v + Om1 * μ') (D.F + 1) < veblen (Om1 * Om1 * v + Om1 * μ) (D.F + 1) :=
  hd_veb_left_lt ((add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left h gv_Om1_pos)) _

variable (hS0 : HnWShape (hoW D (Kf.K 0).Λ (Kf.good gv_Om1_pos)) 0 S0) (hS0γ : S0.γ = max D.γ (Kf.K 0).Λ.g)
include hS0 hS0γ

/-- **THE INVARIANT**: every `hoRGS μ`, `μ < Ω₁`, is a start over `hoW D (Kf.K μ)` with base gate `max γ g_μ`, and
extends every `hoRGS μ'`, `μ' < μ`. -/
theorem hoRGS_inv : ∀ μ (hμ : μ < Om1), (HnWShape (hoW D (Kf.K μ).Λ (Kf.good hμ)) 0 (hoRGS Kf D S0 μ) ∧
    (hoRGS Kf D S0 μ).γ = max D.γ (Kf.K μ).Λ.g) ∧
    ∀ μ', μ' < μ → ∀ c x, c < (hoRGS Kf D S0 μ').B → (hoRGS Kf D S0 μ).R c x = (hoRGS Kf D S0 μ').R c x ∧
      (hoRGS Kf D S0 μ).g c = (hoRGS Kf D S0 μ').g c := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0
    rw [hoRGS_zero]
    exact ⟨⟨hS0, hS0γ⟩, fun μ' h => absurd h (not_lt.2 zero_le)⟩
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hνε : ν < Om1 := (lt_add_one ν).trans hμ
    obtain ⟨⟨hsh, hγ⟩, hext⟩ := IH ν (lt_add_one ν) hνε
    have e : hoRGS Kf D S0 (ν + 1) =
        hnwU (hoW D (Kf.K ν).Λ (Kf.good hνε)) (Kf.K ν).St0 (Kf.K ν).h0 (hoRGS Kf D S0 ν) hsh := by
      rw [hoRGS_succ]; unfold hoRSucc; rw [dif_pos hνε, dif_pos hsh]
    have eΛ : (Kf.K ν).Λ.succ = (Kf.K (ν + 1)).Λ := by rw [Kf.succ]; rfl
    refine ⟨⟨?_, by rw [e, Kf.succ]; rfl⟩, fun μ' hμ' c x hc => ?_⟩
    · rw [e]
      exact hoW_congr D _ (Kf.good_succ hνε) eΛ (Kf.good hμ)
        (hoWU_shape D (Kf.K ν).Λ (Kf.good hνε) (Kf.good_succ hνε) (Kf.K ν).St0 (Kf.K ν).h0 _ hsh)
    · rw [e]
      rcases (Order.lt_add_one_iff.1 hμ').lt_or_eq with hlt | heq
      · obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' (hlt.trans (lt_add_one ν)) (hlt.trans hνε)
        have hc0 : c < (hoRGS Kf D S0 ν).B := by
          rw [hoRGS_Bsh Kf D hνε hsh]; rw [hoRGS_Bsh Kf D (hlt.trans hνε) hsh'] at hc
          exact hc.trans (hoR_veb_lt D hlt)
        obtain ⟨r1, g1⟩ := hext μ' hlt c x hc
        exact ⟨(hnwU_R0 (hoW D (Kf.K ν).Λ (Kf.good hνε)) (Kf.K ν).St0 (Kf.K ν).h0 _ hsh hc0 x).trans r1,
          (hnwU_g0 (hoW D (Kf.K ν).Λ (Kf.good hνε)) (Kf.K ν).St0 (Kf.K ν).h0 _ hsh hc0).trans g1⟩
      · subst heq
        exact ⟨hnwU_R0 (hoW D (Kf.K μ').Λ (Kf.good hνε)) (Kf.K μ').St0 (Kf.K μ').h0 _ hsh hc x,
          hnwU_g0 (hoW D (Kf.K μ').Λ (Kf.good hνε)) (Kf.K μ').St0 (Kf.K μ').h0 _ hsh hc⟩
  · have hcoh : HoRCoh Kf D μ (fun μ' _ => hoRGS Kf D S0 μ') :=
      ⟨fun μ' h hμ' => (IH μ' h hμ').1, fun μ₁ μ₂ h₁ h₂ h12 => (IH μ₂ h₂ (h₂.trans hμ)).2 μ₁ h12⟩
    have e : hoRGS Kf D S0 μ = (hoRCh Kf D μ hlim hμ (fun μ' _ => hoRGS Kf D S0 μ') hcoh).U := by
      rw [hoRGS_limit Kf D S0 hlim]; unfold hoRLimF; rw [dif_pos ⟨hμ, hcoh⟩]
    refine ⟨⟨by rw [e]; exact hoRCh_shape Kf D μ hlim hμ _ hcoh, by rw [e, Kf.lim μ hlim hμ]; rfl⟩,
      fun μ' hμ' c x hc => ?_⟩
    rw [e]
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hμ) μ' hμ'
    have hkl := heFs_lt hlim (hl_om hμ) k
    obtain ⟨⟨hsh', -⟩, -⟩ := IH μ' hμ' (hμ'.trans hμ)
    obtain ⟨-, hextk⟩ := IH _ hkl (hkl.trans hμ)
    have hc' : c < (hoRGS Kf D S0 (heFs μ k)).B := by
      rw [hoRCoh_B Kf D μ hlim hμ _ hcoh k]; rw [hoRGS_Bsh Kf D (hμ'.trans hμ) hsh'] at hc
      exact hc.trans (hoR_veb_lt D hk)
    obtain ⟨r2, g2⟩ := hextk μ' hk c x hc
    exact ⟨((hoRCh Kf D μ hlim hμ (fun μ' _ => hoRGS Kf D S0 μ') hcoh).U_R (k := k) hc' x).trans r2,
      ((hoRCh Kf D μ hlim hμ (fun μ' _ => hoRGS Kf D S0 μ') hcoh).U_g (k := k) hc').trans g2⟩

theorem hoRGS_shape {μ : Ordinal.{0}} (hμ : μ < Om1) :
    HnWShape (hoW D (Kf.K μ).Λ (Kf.good hμ)) 0 (hoRGS Kf D S0 μ) := (hoRGS_inv Kf D S0 hS0 hS0γ μ hμ).1.1

theorem hoRGS_γ {μ : Ordinal.{0}} (hμ : μ < Om1) : (hoRGS Kf D S0 μ).γ = max D.γ (Kf.K μ).Λ.g :=
  (hoRGS_inv Kf D S0 hS0 hS0γ μ hμ).1.2

/-- **The bound of `hoRGS μ` is `φ(Ω₁²·v + Ω₁·μ, F+1)`.** -/
theorem hoRGS_B {μ : Ordinal.{0}} (hμ : μ < Om1) :
    (hoRGS Kf D S0 μ).B = veblen (Om1 * Om1 * v + Om1 * μ) (D.F + 1) :=
  hoRGS_Bsh Kf D hμ (hoRGS_shape Kf D S0 hS0 hS0γ hμ)

theorem hoRGS_ext {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' < μ) {c : Ordinal.{0}}
    (hc : c < (hoRGS Kf D S0 μ').B) (x : Ordinal.{0}) :
    (hoRGS Kf D S0 μ).R c x = (hoRGS Kf D S0 μ').R c x ∧ (hoRGS Kf D S0 μ).g c = (hoRGS Kf D S0 μ').g c :=
  (hoRGS_inv Kf D S0 hS0 hS0γ μ hμ).2 μ' h c x hc

theorem hoRGS_ext' {μ' μ : Ordinal.{0}} (hμ : μ < Om1) (h : μ' ≤ μ) {c : Ordinal.{0}}
    (hc : c < (hoRGS Kf D S0 μ').B) (x : Ordinal.{0}) :
    (hoRGS Kf D S0 μ).R c x = (hoRGS Kf D S0 μ').R c x ∧ (hoRGS Kf D S0 μ).g c = (hoRGS Kf D S0 μ').g c := by
  rcases h.lt_or_eq with h | rfl
  · exact hoRGS_ext Kf D S0 hS0 hS0γ hμ h hc x
  · exact ⟨rfl, rfl⟩

/-- **The base reading of `hoRGS μ` at `μ < x`**: `φ(x·x·v + x·μ, F(x)+1)`. -/
theorem hoRGS_b {μ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : D.γ < x) (hvx : hlGt v < x) (hμ : μ < x) :
    (hoRGS Kf D S0 μ).b x = hdNx (x * x * v + x * μ) (D.Fr x) := by
  have hμ1 : μ < Om1 := hμ.trans hx1
  have hg := Kf.g_lt_x hx hvx hμ hμ1
  rw [(hoRGS_shape Kf D S0 hS0 hS0γ hμ1).2.2.1 x hx hx1 (max_lt (max_lt hγ hg) hx.pos)]
  show veblen ((Kf.K μ).Λ.l x + 0) (D.Fr x + 1) = _
  rw [Kf.l μ hμ1 x hg, add_zero, hoD_b_eq D hx hx1 hγ hvx hμ]

/-- **`b < Ω₁²·v + Ω₁·λ` (`λ` a limit) gives `hcN b F < φ(Ω₁²·v + Ω₁·μ, F+1)` for some `μ < λ`.** -/
theorem hoRGS_Bcof {l b : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l ≤ Om1) (hb : b < Om1 * Om1 * v + Om1 * l) :
    ∃ μ, μ < l ∧ hcN b D.F < (hoRGS Kf D S0 μ).B := by
  rcases lt_or_ge b (Om1 * Om1 * v) with h | h
  · refine ⟨0, hl.bot_lt, ?_⟩
    rw [hoRGS_B Kf D S0 hS0 hS0γ gv_Om1_pos, hoD_B_eq D gv_Om1_pos]
    refine hdN_lt_Nx ?_
    rw [mul_zero, add_zero]; exact ho_sqv_succ gl_Om1_lim hv1 h
  · obtain ⟨b', rfl⟩ := exists_add_of_le h
    have hb' : b' < Om1 * l := (add_lt_add_iff_left _).1 hb
    have hdiv : b' / Om1 < l := (lt_mul_iff_div_lt gv_Om1_pos.ne').1 hb'
    have hμ : b' / Om1 + 1 + 1 < l := hl.add_one_lt (hl.add_one_lt hdiv)
    refine ⟨_, hμ, ?_⟩
    rw [hoRGS_B Kf D S0 hS0 hS0γ (hμ.trans_le hle), hoD_B_eq D (hμ.trans_le hle)]
    refine hdN_lt_Nx ?_
    rw [add_assoc]
    refine (add_lt_add_iff_left _).2 ?_
    calc b' + 1 ≤ Om1 * (b' / Om1) + Om1 := Order.add_one_le_of_lt (lt_mul_div_add b' gv_Om1_pos.ne')
    _ = Om1 * (b' / Om1 + 1) := by rw [mul_add_one]
    _ < Om1 * (b' / Om1 + 1 + 1) := mul_lt_mul_of_pos_left (lt_add_one _) gv_Om1_pos

/-- **SMALL**: a code of `hoRGS μ` with gate below an `ε`-number `σ` lies in some `hoRGS μ'`, `μ' < σ`. -/
theorem hoR_small : ∀ μ, μ < Om1 → ∀ c, c < (hoRGS Kf D S0 μ).B → ∀ σ, InE σ → σ < Om1 →
    (hoRGS Kf D S0 μ).g c < σ → ∃ μ', μ' < σ ∧ c < (hoRGS Kf D S0 μ').B := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ c hc σ hσ hσ1 hg
  by_cases hμσ : μ < σ
  · exact ⟨μ, hμσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hμσ
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hν1 : ν < Om1 := (lt_add_one ν).trans hμ
    by_cases hcν : c < (hoRGS Kf D S0 ν).B
    · rw [(hoRGS_ext Kf D S0 hS0 hS0γ hμ (lt_add_one ν) hcν 0).2] at hg
      exact IH ν (lt_add_one ν) hν1 c hcν σ hσ hσ1 hg
    · exfalso
      have hsh := hoRGS_shape Kf D S0 hS0 hS0γ hν1
      have e : hoRGS Kf D S0 (ν + 1) =
          hnwU (hoW D (Kf.K ν).Λ (Kf.good hν1)) (Kf.K ν).St0 (Kf.K ν).h0 (hoRGS Kf D S0 ν) hsh := by
        rw [hoRGS_succ]; unfold hoRSucc; rw [dif_pos hν1, dif_pos hsh]
      rw [e] at hc hg
      have h := hnwU_highR _ _ _ _ hsh (not_lt.1 hcν) hc hσ hσ1 hg
      exact hμσ ((ev_isSuccLimit_of_inE hσ).add_one_lt (Kf.glt ν hν1 σ hσ ((le_max_right _ _).trans_lt h)))
  · have hcS : c < veblen (Om1 * Om1 * v + Om1 * μ) (D.F + 1) := by
      rw [← hoRGS_B Kf D S0 hS0 hS0γ hμ]; exact hc
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hoL_ne hv1 gl_Om1_E) (hoD_Ffix D hμ) hcS
    obtain ⟨μ'', hμ'', hbμ⟩ := hoRGS_Bcof Kf D S0 hS0 hS0γ hlim hμ.le hb
    have hcμ : c < (hoRGS Kf D S0 μ'').B := hcb.trans hbμ
    rw [(hoRGS_ext Kf D S0 hS0 hS0γ hμ hμ'' hcμ 0).2] at hg
    exact IH μ'' hμ'' (hμ''.trans hμ) c hcμ σ hσ hσ1 hg

/-- **HIGH**: a code of `hoRGS μ` past the start `S₀` with gate below an `ε`-number `σ` forces `hlGt v < σ`. -/
theorem hoR_high : ∀ μ, μ < Om1 → ∀ c, S0.B ≤ c → c < (hoRGS Kf D S0 μ).B → ∀ σ, InE σ → σ < Om1 →
    (hoRGS Kf D S0 μ).g c < σ → hlGt v < σ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ c hSc hc σ hσ hσ1 hg
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨ν, hν⟩ | hlim
  · subst h0; rw [hoRGS_zero] at hc; exact absurd hc (not_lt.2 hSc)
  · have hν' : μ = ν + 1 := by rw [← hν, succ_eq_add_one]
    subst hν'
    have hν1 : ν < Om1 := (lt_add_one ν).trans hμ
    by_cases hcν : c < (hoRGS Kf D S0 ν).B
    · rw [(hoRGS_ext Kf D S0 hS0 hS0γ hμ (lt_add_one ν) hcν 0).2] at hg
      exact IH ν (lt_add_one ν) hν1 c hSc hcν σ hσ hσ1 hg
    · have hsh := hoRGS_shape Kf D S0 hS0 hS0γ hν1
      have e : hoRGS Kf D S0 (ν + 1) =
          hnwU (hoW D (Kf.K ν).Λ (Kf.good hν1)) (Kf.K ν).St0 (Kf.K ν).h0 (hoRGS Kf D S0 ν) hsh := by
        rw [hoRGS_succ]; unfold hoRSucc; rw [dif_pos hν1, dif_pos hsh]
      rw [e] at hc hg
      have h := hnwU_highR _ _ _ _ hsh (not_lt.1 hcν) hc hσ hσ1 hg
      exact (Kf.glo ν hν1).trans_lt ((le_max_right _ _).trans_lt h)
  · have hcS : c < veblen (Om1 * Om1 * v + Om1 * μ) (D.F + 1) := by
      rw [← hoRGS_B Kf D S0 hS0 hS0γ hμ]; exact hc
    obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hoL_ne hv1 gl_Om1_E) (hoD_Ffix D hμ) hcS
    obtain ⟨μ'', hμ'', hbμ⟩ := hoRGS_Bcof Kf D S0 hS0 hS0γ hlim hμ.le hb
    have hcμ : c < (hoRGS Kf D S0 μ'').B := hcb.trans hbμ
    rw [(hoRGS_ext Kf D S0 hS0 hS0γ hμ hμ'' hcμ 0).2] at hg
    exact IH μ'' hμ'' (hμ''.trans hμ) c hSc hcμ σ hσ hσ1 hg

/-! ## The union -/

/-- **THE FAMILY `hoRGS μ`, `μ < Ω₁`, AS AN `Ho.HoFam`**: union bound `hdNx (Ω₁²·(v+1)) F`, gate
`max γ (hlGt v)`, base reading `hdNx (x·x·(v+1)) (F(x))`, low field `D.Zo`. -/
noncomputable def hoRFam : HoFam where
  D := hoRGS Kf D S0
  B := hdNx (Om1 * Om1 * (v + 1)) D.F
  γ := max D.γ (hlGt (v + 1))
  b := fun x => hdNx (x * x * (v + 1)) (D.Fr x)
  Zo := D.Zo
  γ_lt := max_lt D.γ_lt ((hlGt_le _).trans_lt (gl_Om1_lim.add_one_lt hv))
  γ_cl := D.S_cl
  G_lt := D.G_le.trans_lt (hdNx_gt _ _)
  B_E := ho_next_E D
  B_lt1 := D.S_lt1
  B_fix1 := hdNx_fix (one_lt_omega0.trans ((omega0_lt_inE gl_Om1_E).trans (ho_x_lt_next gl_Om1_E))) _
  B_mem := fun S a b ha hb => D.S_mem S ha
    (max_lt_iff.2 ⟨(max_lt_iff.1 hb).1, (ho_hlGt_le_succ v).trans_lt (max_lt_iff.1 hb).2⟩)
  DB_lt := fun μ hμ => by
    rw [hoRGS_B Kf D S0 hS0 hS0γ hμ, hoD_B_eq D hμ]
    exact (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (hoL_succ_lt_next gl_Om1_E hμ))
  B_cof := fun c hc => by
    obtain ⟨b, hb, hcb⟩ := hjw_Nx_cof (ho_next_ne gl_Om1_E) D.F_P hc
    rw [mul_add_one] at hb
    obtain ⟨μ, hμ, hbμ⟩ := hoRGS_Bcof Kf D S0 hS0 hS0γ gl_Om1_lim le_rfl hb
    exact ⟨μ, hμ, hcb.trans hbμ⟩
  ext := fun _ _ h hμ c x hc => hoRGS_ext' Kf D S0 hS0 hS0γ hμ h hc x
  small := hoR_small Kf D S0 hS0 hS0γ
  γD := fun x hx hx1 hγ μ hμ => by
    rw [hoRGS_γ Kf D S0 hS0 hS0γ (hμ.trans hx1)]
    exact max_lt (max_lt_iff.1 hγ).1 (Kf.g_lt_x hx (ho_hv' hγ) hμ (hμ.trans hx1))
  bD := fun x hx hx1 hγ μ hμ => by
    rw [hoRGS_b Kf D S0 hS0 hS0γ hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ) hμ]
    exact hoD_b_lt D hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ) hμ
  ZD := fun x hx hx1 hγ μ hμ => by
    have hμ1 : μ < Om1 := hμ.trans hx1
    have hg := Kf.g_lt_x hx (ho_hv' hγ) hμ hμ1
    rw [(hoRGS_shape Kf D S0 hS0 hS0γ hμ1).2.2.2.1 x hx hx1,
      if_pos (show max (hoW D (Kf.K μ).Λ (Kf.good hμ1)).γR 0 < x from max_lt (max_lt (max_lt_iff.1 hγ).1 hg) hx.pos)]
    refine (hb_evZ_lt_fix2 (hdNx_fix (ho_two_lt_next hx) _) ?_).le
    show veblen ((Kf.K μ).Λ.l x + 0) (D.Fr x + 1) < _
    rw [Kf.l μ hμ1 x hg, add_zero, hoD_b_eq D hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ) hμ]
    exact hoD_b_lt D hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ) hμ
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hjw_Nx_cof (ho_next_ne hx) (D.Fr_P hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ)) hν
    rw [mul_add_one] at hb
    obtain ⟨μ, hμ, hb1⟩ := ho_cof_band hx (fun _ h => ho_sqv_succ (ev_isSuccLimit_of_inE hx) hv1 h) hb
    refine ⟨μ, hμ, ?_⟩
    rw [hoRGS_b Kf D S0 hS0 hS0γ hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ) hμ]
    exact hνb.trans (hdN_lt_Nx hb1)
  b_E := fun x hx _ _ => hdNx_E (ho_next_ne hx) _
  x_lt_b := fun x hx hx1 hγ => ((ho_x_lt_next hx).trans_le (D.Fr_gt hx hx1 (max_lt_iff.1 hγ).1
    (ho_hv' hγ))).trans (hdNx_gt _ _)
  b_fix1 := fun x hx _ _ => hdNx_fix (one_lt_omega0.trans ((omega0_lt_inE hx).trans (ho_x_lt_next hx))) _
  b_lt1 := fun x hx hx1 hγ => (D.S_Zo hx hx1 (max_lt_iff.1 hγ).1 (ho_hv' hγ)).trans (D.Zo_G1 x hx hx1)
  b_pi := fun _ _ hB hγ => D.S_pi hB
    (max_lt_iff.2 ⟨(max_lt_iff.1 hγ).1, (ho_hlGt_le_succ v).trans_lt (max_lt_iff.1 hγ).2⟩)
  Z_low := fun μ hμ x hx hx1 h => by
    rw [(hoRGS_shape Kf D S0 hS0 hS0γ hμ).2.2.2.1 x hx hx1]
    split_ifs with h'
    · exfalso
      have hg' : max D.γ (Kf.K μ).Λ.g < x := (max_lt_iff.1 h').1
      exact h (max_lt (max_lt_iff.1 hg').1 (ho_hlGt_succ_lt hx ((Kf.glo μ hμ).trans_lt (max_lt_iff.1 hg').2)))
    · rw [hoW_Zo_low D _ _ (fun h'' => h' (max_lt h'' hx.pos))]
  Zo_fix := D.Zo_fix
  Zo_G1 := D.Zo_G1

/-- **THE UNION OF ALL `hoRGS μ`, `μ < Ω₁`**: a gated digit system with the bound `hdNx (Ω₁²·(v+1)) F`. -/
noncomputable def hoRU : HgVD := hoOU (hoRFam Kf D S0 hS0 hS0γ)

theorem hoRU_B : (hoRU Kf D S0 hS0 hS0γ).B = hdNx (Om1 * Om1 * (v + 1)) D.F := rfl

theorem hoRU_γ : (hoRU Kf D S0 hS0 hS0γ).γ = max D.γ (hlGt (v + 1)) := rfl

theorem hoRU_b (x : Ordinal.{0}) : (hoRU Kf D S0 hS0 hS0γ).b x = hdNx (x * x * (v + 1)) (D.Fr x) := rfl

theorem hoRU_Z (x : Ordinal.{0}) : (hoRU Kf D S0 hS0 hS0γ).Z x =
    if max D.γ (hlGt (v + 1)) < x then evZ (hdNx (x * x * (v + 1)) (D.Fr x)) else D.Zo x := rfl

theorem hoRU_R {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hoRGS Kf D S0 μ).B) (x : Ordinal.{0}) :
    (hoRU Kf D S0 hS0 hS0γ).R c x = (hoRGS Kf D S0 μ).R c x := hoOU_R _ hμ hc x

theorem hoRU_g {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (hoRGS Kf D S0 μ).B) :
    (hoRU Kf D S0 hS0 hS0γ).g c = (hoRGS Kf D S0 μ).g c := hoOU_g _ hμ hc

/-- **The union extends the start `S₀`.** -/
theorem hoRU_ext0 {c : Ordinal.{0}} (hc : c < S0.B) (x : Ordinal.{0}) :
    (hoRU Kf D S0 hS0 hS0γ).R c x = S0.R c x ∧ (hoRU Kf D S0 hS0 hS0γ).g c = S0.g c := by
  have hc' : c < (hoRGS Kf D S0 0).B := by rw [hoRGS_zero]; exact hc
  rw [hoRU_R Kf D S0 hS0 hS0γ gv_Om1_pos hc', hoRU_g Kf D S0 hS0 hS0γ gv_Om1_pos hc', hoRGS_zero]
  exact ⟨rfl, rfl⟩

/-- **HIGH for the union**: a code of the union past `S₀` with gate below an `ε`-number `σ` forces
`hlGt v < σ`. -/
theorem hoRU_high {c σ : Ordinal.{0}} (hSc : S0.B ≤ c) (hc : c < (hoRU Kf D S0 hS0 hS0γ).B) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hoRU Kf D S0 hS0 hS0γ).g c < σ) : hlGt v < σ := by
  obtain ⟨n, hn1, hn⟩ := (hoRFam Kf D S0 hS0 hS0γ).B_cof c hc
  rw [hoRU_g Kf D S0 hS0 hS0γ hn1 hn] at hg
  exact hoR_high Kf D S0 hS0 hS0γ n hn1 c hSc hn σ hσ hσ1 hg

/-- **The union has the high condition of its members**: a code past `F` with gate below `σ` forces `γ < σ`. -/
theorem hoRU_highF {c σ : Ordinal.{0}} (hFc : D.F ≤ c) (hc : c < (hoRU Kf D S0 hS0 hS0γ).B) (hσ : InE σ)
    (hσ1 : σ < Om1) (hg : (hoRU Kf D S0 hS0 hS0γ).g c < σ) : D.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := (hoRFam Kf D S0 hS0 hS0γ).B_cof c hc
  rw [hoRU_g Kf D S0 hS0 hS0γ hn1 hn] at hg
  exact (hoRGS_shape Kf D S0 hS0 hS0γ hn1).2.2.2.2 c σ hFc hn hσ hσ1 hg

end BR

end Googology.Trans.PoR.InaccPsi.R2.Ho
