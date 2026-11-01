import Googology.Trans.PoR.InaccPsi.R2.XlW

/-!
# XpBand: THE LEVELS `L + κ` (`κ < Ω₁`) OF A GENERAL (A3) BAND, AND THE `Ω₁`-UNION `φ(L + Ω₁, 0)`

The band step of `Xl.XlK` / `Xl.XlKRec` / `Xl.XlW` (written there for the band `G`) for an arbitrary band datum:

* `XpBd0` (**A BASIC BAND DATUM**: a package `K : Hn.HnPk` whose level `L` lies above `G` and whose reading is not
  strongly critical above the gate; enough for the level `t₀`), `XpBd` (**A BAND DATUM**: in addition the reading lies
  below `ε_{Γ_{x+1}+1}`), `XpBd.succ` (the band `L + Ω₁`);
* `xpZ` (the common low field `N_{ε_{Γ_{x+1}+1}}(0)` of every band), `xpBK` (**THE BOTTOM BASE OF THE LEVEL `L + κ`**:
  shift `0`, gate `max κ g`), `XpAt` (**`U` IS A SYSTEM AT THE BOTTOM `φ(L + κ, 0)`**), `xp_start_of_at`,
  `xp_at_top` (**THE TOP OF THE LEVEL `L + κ` IS A SYSTEM AT `φ(L + κ + 1, 0)`**).

No new axiom.  New definitions: `XpBd0`, `XpBd`, `XpBd.succ`, `xpZ`, `xpBK`, `XpAt`, `xpSt`.
-/

set_option autoImplicit false


open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
  Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Wy
  Googology.Trans.PoR.InaccPsi.R2.Wx


open Googology.Trans.PoR.InaccPsi.R2.Xc
open Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Xf

open Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Xl

namespace Googology.Trans.PoR.InaccPsi.R2.Xp

/-! ## The band datum -/

/-- **A BASIC BAND DATUM**: a package `K` at the level `L = K.Λ.L > G` whose reading `ℓ(x)` (above the gate `g`) is
not strongly critical (enough for the bottom base and the top of each level `L + κ`). -/
structure XpBd0 where
  K : HnPk
  G_lt : gcG 0 < K.Λ.L
  l_nsc : ∀ x, InE x → x < Om1 → K.Λ.g < x → K.Λ.l x < veblen (K.Λ.l x) 0

/-- **A BAND DATUM**: a basic band datum whose reading lies below `ε_{Γ_{x+1}+1}` (the bands below `t₀`). -/
structure XpBd extends XpBd0 where
  l_lt : ∀ x, InE x → x < Om1 → K.Λ.g < x → K.Λ.l x < wnLv3T0.l x

theorem xp_aE {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : InE (wnLv3T0.l x) := by
  rw [wnLv3T0_l hx hx1]; exact eN_E _

theorem xp_x_lt_a {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x < wnLv3T0.l x :=
  (lgG_facts hx hx1).2.1.trans (wnLv3T0.l_gtG x hx hx1 hx.pos)

theorem xp_lt_sum {a x : Ordinal.{0}} (hx : 0 < x) (hxa : x ≤ a) : x < a + x :=
  hxa.trans_lt (lt_add_of_pos_right _ hx)

/-- **The next band datum `L + Ω₁`** (reading `ℓ(x) + x`, package `HnPk.succ`). -/
noncomputable def XpBd.succ (B : XpBd) : XpBd where
  K := B.K.succ
  G_lt := B.G_lt.trans_le le_self_add
  l_nsc := fun x hx _ _ => xl_lt_veb0 hx.pos (xp_lt_sum hx.pos (B.K.Λ.l_ge x))
  l_lt := fun x hx hx1 hg => (inE_indec (xp_aE hx hx1)).add_lt (B.l_lt x hx hx1 hg) (xp_x_lt_a hx hx1)

theorem XpBd.succ_Λ (B : XpBd) : B.succ.K.Λ = B.K.Λ.succ := rfl

/-! ## Readings and the low field -/

/-- **`ℓ(x) + κ < φ(ℓ(x) + κ, 0)`** for `κ < x` above the gate. -/
theorem xp_lt_veb0 (B : XpBd0) {x κ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.K.Λ.g < x) (hκx : κ < x) :
    B.K.Λ.l x + κ < veblen (B.K.Λ.l x + κ) 0 := by
  rcases eq_or_ne κ 0 with rfl | hκ0
  · rw [add_zero]; exact B.l_nsc x hx hx1 hg
  · exact xl_lt_veb0 (pos_iff_ne_zero.2 hκ0) (hκx.trans_le ((B.K.Λ.l_ge x).trans le_self_add))

theorem xp_N_lt1 (Λ : HnLv) {x κ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hκx : κ < x) :
    hcN (Λ.l x + κ) 0 < gq 1 x :=
  he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hnv_q Λ hx hx1 hκx))
    (gm1_facts hx hx1).2.2.2.pos

theorem xp_L1_lt (Λ : HnLv) {κ : Ordinal.{0}} (hκ : κ < Om1) : Λ.L + κ + 1 < gcG 1 := by
  have hE := Low.opow_eq_self_of_SC (gcG_SC 1)
  exact (ev_isSuccLimit_of_inE hE).add_one_lt ((inE_indec hE).add_lt Λ.L_G
    (hκ.trans (gl_Om1_lt_G0.trans (gcG_lt zero_lt_one))))

/-- **`ϑˣ(Ω₁·(ℓ(x) + κ) + t) = φ(ℓ(x) + κ, t)`** below `N_{ℓ(x)+κ}(0)` (`κ < x`, above the gate). -/
theorem xp_glA (B : XpBd0) {x κ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.K.Λ.g < x) (hκx : κ < x) :
    ∀ t, t < hcN (B.K.Λ.l x + κ) 0 → glA (B.K.Λ.l x + κ) t x = veblen (B.K.Λ.l x + κ) t :=
  xl_glAv hx hx1 (hnv_one B.K.Λ hx hx1 hκx) (hnv_q B.K.Λ hx hx1 hκx) (hnv_xl B.K.Λ hx hx1)
    (xp_lt_veb0 B hx hx1 hg hκx) (xp_N_lt1 B.K.Λ hx hx1 hκx)

/-- **THE COMMON LOW FIELD OF EVERY BAND**: `N_{a(x)}(0) = φ(a(x) + 1, 0)`, `a(x) = ε_{Γ_{x+1}+1}` (`x` read as
`max ω x`). -/
noncomputable def xpZ (x : Ordinal.{0}) : Ordinal.{0} := hcN (wnLv3T0.l (max ω x)) 0

theorem xpZ_eq {x : Ordinal.{0}} (hx : InE x) : xpZ x = hcN (wnLv3T0.l x) 0 := by
  unfold xpZ; rw [max_eq_right (omega0_lt_inE hx).le]

theorem xp_two_le_a (x : Ordinal.{0}) : (2 : Ordinal.{0}) ≤ wnLv3T0.l (max ω x) :=
  (show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
    ((le_max_left ω x).trans (wnLv3T0.l_ge _))

theorem xpZ_fix (x : Ordinal.{0}) : veblen 2 (xpZ x) = xpZ x := hc_fix_down (xp_two_le_a x) (hcN_fix _ _)

theorem xpZ_fix1 (x : Ordinal.{0}) : veblen 1 (xpZ x) = xpZ x :=
  hc_fix_down (one_le_two.trans (xp_two_le_a x)) (hcN_fix _ _)

theorem xpZ_G1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : xpZ x < gq 1 x := by
  rw [xpZ_eq hx]
  exact he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt
    (wnLv3T0.l_lt x hx hx1)) (gm1_facts hx hx1).2.2.2.pos

/-- **Every bottom `φ(ℓ(x) + μ, 0)` (`μ < x`) of a band lies below the low field.** -/
theorem xp_veb_lt_Z (B : XpBd) {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.K.Λ.g < x) (hμx : μ < x) :
    veblen (B.K.Λ.l x + μ) 0 < xpZ x := by
  rw [xpZ_eq hx, xl_N_eq]
  refine veblen_zero_lt_veblen_zero.2 (lt_of_lt_of_le ?_ (le_add_right le_rfl))
  exact (inE_indec (xp_aE hx hx1)).add_lt (B.l_lt x hx hx1 hg) (hμx.trans (xp_x_lt_a hx hx1))

/-! ## The bottom base of the level `L + κ` -/

/-- **THE BOTTOM BASE OF THE LEVEL `L + κ`** (`κ < Ω₁`): shift `0`, reading gate `max κ g`, low field `xpZ`. -/
noncomputable def xpBK (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) : XlB B.K.Λ κ where
  e := 0
  γN := max κ B.K.Λ.g
  Zo := xpZ
  lv := hκ
  lvN := le_max_left _ _
  lg := le_max_right _ _
  γN_lt := max_lt hκ B.K.Λ.g_lt
  G_lt := by
    rw [Nat.cast_zero]
    exact B.G_lt.trans_le (le_self_add.trans (left_le_veblen _ 0))
  N_lt1 := by
    rw [xl_N_eq]
    have h := (isNormal_veblen (B.K.Λ.L + κ + 1)).strictMono (gcG_SC 1).1
    rwa [gn_veb_fix (gcG_SC 1) (xp_L1_lt B.K.Λ hκ)] at h
  N_mem := fun S _ _ ha hb => by
    rw [xl_N_eq]
    exact CSet.phi_mem (CSet.succ_mem (hnv_L_mem B.K.Λ S ha ((le_max_right _ _).trans_lt hb)
      ((le_max_left _ _).trans_lt hb))) (CSet.zero_mem _ _)
  N_cl := fun Z hZ hZ1 h => by
    rw [xl_N_eq, add_assoc] at h
    have hκ1 : κ + 1 < Om1 := gl_Om1_lim.add_one_lt hκ
    have hGQ : gcG 0 < veblen (B.K.Λ.L + (κ + 1)) 0 := B.G_lt.trans_le (le_self_add.trans (left_le_veblen _ 0))
    have hs : veblen (B.K.Λ.L + (κ + 1)) 0 < veblen (B.K.Λ.L + (κ + 1)) (0 + 1) :=
      (isNormal_veblen _).strictMono (show (0 : Ordinal.{0}) < 0 + 1 by rw [zero_add]; exact zero_lt_one)
    exact max_lt ((lt_add_one κ).trans (hnv_cl_gate B.K.Λ hκ1 hZ hZ1 veblen_pos hGQ h le_rfl hs))
      (hnv_cl_g B.K.Λ hκ1 hZ hZ1 veblen_pos hGQ h le_rfl hs)
  γN_cl := fun _ _ _ h hg => max_lt h hg
  Zo_fix := xpZ_fix
  Zo_G1 := fun _ hx hx1 => xpZ_G1 hx hx1
  read := fun {x} hx hx1 hγ t ht => by
    rw [Nat.cast_zero, zero_add]
    exact xp_glA B hx hx1 ((le_max_right _ _).trans_lt hγ) ((le_max_left _ _).trans_lt hγ) t ht
  N_pi := fun hB hγ => xl_N_pi_gen B.K.Λ hB ((le_max_right _ _).trans_lt hγ) ((le_max_left _ _).trans_lt hγ)

theorem xpBK_e (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) : (((xpBK B κ hκ).e : ℕ) : Ordinal.{0}) = 0 :=
  Nat.cast_zero

theorem xpBK_γN (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) : (xpBK B κ hκ).γN = max κ B.K.Λ.g := rfl

/-! ## Systems at the bottom `φ(L + κ, 0)` -/

/-- **`U` IS A SYSTEM AT THE BOTTOM `φ(L + κ, 0)` OF THE LEVEL `L + κ`** (gate `max κ g`, low field `xpZ`). -/
structure XpAt (Λ : HnLv) (κ : Ordinal.{0}) (U : HgVD) : Prop where
  B : U.B = veblen (Λ.L + κ) 0
  ix : U.ix = veblen (Λ.L + κ) 0
  γ : ∀ x, InE x → x < Om1 → (U.γ < x ↔ max κ Λ.g < x)
  b : ∀ x, InE x → x < Om1 → max κ Λ.g < x → U.b x = veblen (Λ.l x + κ) 0
  γ_le : U.γ ≤ max κ Λ.g
  Z : ∀ x, InE x → x < Om1 → U.Z x = if max κ Λ.g < x then evZ (veblen (Λ.l x + κ) 0) else xpZ x

/-- **A SYSTEM AT `φ(L + κ, 0)` STARTS THE BOTTOM RECURSION OF THE LEVEL `L + κ`.** -/
theorem xp_start_of_at (B : XpBd0) {κ : Ordinal.{0}} (hκ : κ < Om1) {U : HgVD} (hU : XpAt B.K.Λ κ U) :
    XlStart (xpBK B κ hκ) U where
  B := by rw [hU.B, xpBK_e, add_zero]
  Zb := fun x hx hx1 => by
    rw [hU.Z x hx hx1]
    by_cases h : max κ B.K.Λ.g < x
    · rw [if_pos h, (xpBK B κ hκ).Zl_eq hx h, xl_N_eq]
      have h2 : (2 : Ordinal.{0}) < B.K.Λ.l x + κ + 1 :=
        ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
          (hnv_ωl B.K.Λ hx hx1).le).trans_lt (lt_add_one _)
      exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt h2 0) (veblen_zero_lt_veblen_zero.2 (lt_add_one _))).le
    · rw [if_neg h, (xpBK B κ hκ).Zl_low h]; rfl
  st := fun h2 hZ => by
    refine ⟨?_, fun x hx hx1 => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 => ?_⟩
    · show U.ix = veblen (B.K.Λ.L + κ) ((xpBK B κ hκ).e + 0)
      rw [hU.ix, xpBK_e, add_zero]
    · show U.γ < x ↔ max (max κ B.K.Λ.g) (U.g 0) < x
      rw [U.g_zero, max_eq_left zero_le]; exact hU.γ x hx hx1
    · have hκx : max κ B.K.Λ.g < x := (max_lt_iff.1 hg).1
      show U.b x = glA (B.K.Λ.l x + κ) (U.R 0 x) x
      rw [U.R_zero, (xpBK B κ hκ).read hx hx1 hκx 0 (hcN_E _ _).pos, xpBK_e, add_zero, hU.b x hx hx1 hκx]
    · rw [hU.Z x hx hx1]
      show _ = HgPB.Zst _ x
      by_cases h : max κ B.K.Λ.g < x
      · have hg : max (max κ B.K.Λ.g) (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_pos h, HgPB.Zst_eq _ hg]
        show evZ (veblen (B.K.Λ.l x + κ) 0) = evZ (glA (B.K.Λ.l x + κ) (U.R 0 x) x)
        rw [U.R_zero, (xpBK B κ hκ).read hx hx1 h 0 (hcN_E _ _).pos, xpBK_e, add_zero]
      · have hg : ¬ max (max κ B.K.Λ.g) (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_neg h, HgPB.Zst_low _ hg]
        show xpZ x = (xpBK B κ hκ).Zl x
        rw [(xpBK B κ hκ).Zl_low h]; rfl

/-! ## The step and the top of a level -/

/-- **The step at the level `L + κ`**: `Hn.hnVLS` of the package of the band. -/
noncomputable abbrev xpSt (B : XpBd0) (κ : Ordinal.{0}) : HnVStTy B.K.Λ κ := hnVLS B.K.St0 κ

theorem xpSt_spec (B : XpBd0) {κ : Ordinal.{0}} (hκ : κ < Om1) : ∀ Q U h, HnVSpec Q U (xpSt B κ Q U h) :=
  fun Q U h => hnVLS_spec B.K.St0 B.K.h0 hκ Q U h

theorem xp_max_succ {κ g x : Ordinal.{0}} (hx : InE x) : max κ g < x ↔ max (κ + 1) g < x := by
  rw [max_lt_iff, max_lt_iff]
  exact ⟨fun h => ⟨(ev_isSuccLimit_of_inE hx).add_one_lt h.1, h.2⟩,
    fun h => ⟨(lt_add_one κ).trans h.1, h.2⟩⟩

/-- **THE TOP OF THE LEVEL `L + κ` IS A SYSTEM AT `φ(L + κ + 1, 0)`.** -/
theorem xp_at_top (B : XpBd0) {κ : Ordinal.{0}} (hκ : κ < Om1) {U : HgVD} (hU : XpAt B.K.Λ κ U) :
    XpAt B.K.Λ (κ + 1) (xlTU (xpSt_spec B hκ) (xp_start_of_at B hκ hU)) where
  B := by rw [xlTU_B, xl_N_eq, add_assoc]
  ix := by show hcN (B.K.Λ.L + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ := fun x hx _ => xp_max_succ hx
  b := fun x _ _ _ => by show hcN (B.K.Λ.l x + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ_le := by show max κ B.K.Λ.g ≤ max (κ + 1) B.K.Λ.g; exact max_le_max (lt_add_one κ).le le_rfl
  Z := fun x hx _ => by
    show (if max κ B.K.Λ.g < x then evZ (hcN (B.K.Λ.l x + κ) 0) else xpZ x) = _
    by_cases h : max κ B.K.Λ.g < x
    · rw [if_pos h, if_pos ((xp_max_succ hx).1 h), xl_N_eq, add_assoc]
    · rw [if_neg h, if_neg (fun h' => h ((xp_max_succ hx).2 h'))]

end Googology.Trans.PoR.InaccPsi.R2.Xp
