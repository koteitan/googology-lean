import Googology.Trans.PoR.InaccPsi.R2.XuEnd
import Googology.Trans.PoR.InaccPsi.R2.XpBand

/-!
# XuBand: THE BAND STEP BELOW A BOUND `T ∈ [t₀, Γ(1))`: data, low field, bottom bases, systems at the bottoms

`R2.XpBand` with the bound `ε_{Γ_{x+1}+1}` (the reading of `t₀`) replaced by the reading `xuR T x` of an `ε`-number
code `T ∈ [t₀, Γ(1))` of gate `≤ 1` (every `t_n`, `Xu.xuGg_t`).  The generic parts of `R2.XpBand` (`Xp.XpBd0`,
`Xp.xp_glA`, `Xp.xp_lt_veb0`, `Xp.xp_N_lt1`, `Xp.xp_L1_lt`, `Xp.xpSt`) are used as they are.

* `XuT` (the bound: `InE T`, `t₀ ≤ T < Γ(1)`, `xuG T ≤ 1`), `xuqA` (`max ω (xuR T x)`), `xuq_aE`, `xuq_x_lt_a`,
  `xuq_G_lt_a`, `xuq_a_lt1`;
* `XuqBd T` (**A BAND DATUM BELOW `T`**), `XuqBd.succ`;
* `xuqZ T` (**THE COMMON LOW FIELD `N_{T(x)}(0)` OF EVERY BAND BELOW `T`**), `xuqZ_fix`, `xuqZ_G1`, `xuq_veb_lt_Z`;
* `xuqBK` (the bottom base of the level `L + κ` with the low field `xuqZ T`), `XuqAt` (a system at `φ(L+κ, 0)`),
  `xuq_start_of_at`, `xuq_at_top`.

No new axiom.  New definitions: `XuT`, `xuqA`, `XuqBd`, `XuqBd.succ`, `xuqZ`, `xuqBK`, `XuqAt`.
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
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
open Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gn
open Googology.Trans.PoR.InaccPsi.R2.Xl Googology.Trans.PoR.InaccPsi.R2.Xp

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

/-- **THE BOUND OF THE BANDS**: an `ε`-number code `T ∈ [t₀, Γ(1))` with gate `≤ 1`. -/
structure XuT (T : Ordinal.{0}) : Prop where
  E : InE T
  t0_le : Wj.wjT 0 ≤ T
  lt1 : T < gcG 1
  g_le : xuG T ≤ 1

theorem xuT_t (n : ℕ) : XuT (Wj.wjT n) := by
  refine ⟨(Wj.wjT_spec n).2.2.1, Wj.wjT_mono (Nat.zero_le n), (Wj.wjT_spec n).2.1, ?_⟩
  have := xuGg_t n
  unfold xuGg at this
  rw [← this]; exact le_max_right _ _

/-- **The reading of the bound**, `ω` at the small arguments. -/
noncomputable def xuqA (T x : Ordinal.{0}) : Ordinal.{0} := max ω (xuR T x)

section A

variable {T : Ordinal.{0}} (hT : XuT T) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hT hx hx1

theorem xuq_g_lt : xuG T < x := hT.g_le.trans_lt (wo_one_lt_inE hx)

theorem xuq_read : InE (xuR T x) ∧ eN (lgG x) ≤ xuR T x ∧ xuR T x < gq 1 x := by
  have hg := xuq_g_lt hT hx hx1
  obtain ⟨-, -, hke, hηe, -, -, -, -, -, -, -, hE, -⟩ := xu_eps_read hx hx1 hT.E hT.t0_le hT.lt1 hg
  have hM := xu_mono_top hx hx1
  exact ⟨hE, xu_eps_ge hx hx1 hT.E hT.t0_le hT.lt1 hg (hM _ (hke.trans hT.lt1)).1 (hM _ (hηe.trans hT.lt1)).1,
    xuR_lt1 hx hx1 hT.lt1 hg⟩

theorem xuqA_eq : xuqA T x = xuR T x := by
  unfold xuqA
  exact max_eq_right ((omega0_lt_inE hx).le.trans
    (((lgG_facts hx hx1).2.1.trans (lt_eN _)).le.trans (xuq_read hT hx hx1).2.1))

theorem xuq_aE : InE (xuqA T x) := by rw [xuqA_eq hT hx hx1]; exact (xuq_read hT hx hx1).1

theorem xuq_G_lt_a : lgG x < xuqA T x := by
  rw [xuqA_eq hT hx hx1]; exact (lt_eN _).trans_le (xuq_read hT hx hx1).2.1

theorem xuq_x_lt_a : x < xuqA T x := (lgG_facts hx hx1).2.1.trans (xuq_G_lt_a hT hx hx1)

theorem xuq_a_lt1 : xuqA T x < gq 1 x := by rw [xuqA_eq hT hx hx1]; exact (xuq_read hT hx hx1).2.2

end A

/-! ## The band datum below `T` -/

/-- **A BAND DATUM BELOW `T`**: a basic band datum whose reading lies below the reading of `T`. -/
structure XuqBd (T : Ordinal.{0}) extends XpBd0 where
  hT : XuT T
  l_lt : ∀ x, InE x → x < Om1 → K.Λ.g < x → K.Λ.l x < xuqA T x

/-- **The next band datum `L + Ω₁`** (reading `ℓ(x) + x`, package `HnPk.succ`). -/
noncomputable def XuqBd.succ {T : Ordinal.{0}} (B : XuqBd T) : XuqBd T where
  K := B.K.succ
  hT := B.hT
  G_lt := B.G_lt.trans_le le_self_add
  l_nsc := fun x hx _ _ => xl_lt_veb0 hx.pos (xp_lt_sum hx.pos (B.K.Λ.l_ge x))
  l_lt := fun x hx hx1 hg =>
    (inE_indec (xuq_aE B.hT hx hx1)).add_lt (B.l_lt x hx hx1 hg) (xuq_x_lt_a B.hT hx hx1)

theorem XuqBd.succ_Λ {T : Ordinal.{0}} (B : XuqBd T) : B.succ.K.Λ = B.K.Λ.succ := rfl

/-! ## The low field -/

/-- **THE COMMON LOW FIELD OF EVERY BAND BELOW `T`**: `N_{T(x)}(0) = φ(T(x) + 1, 0)`. -/
noncomputable def xuqZ (T x : Ordinal.{0}) : Ordinal.{0} := hcN (xuqA T (max ω x)) 0

theorem xuq_two_le_a (T x : Ordinal.{0}) : (2 : Ordinal.{0}) ≤ xuqA T (max ω x) :=
  (show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans (le_max_left _ _)

theorem xuqZ_fix (T x : Ordinal.{0}) : veblen 2 (xuqZ T x) = xuqZ T x :=
  hc_fix_down (xuq_two_le_a T x) (hcN_fix _ _)

theorem xuqZ_fix1 (T x : Ordinal.{0}) : veblen 1 (xuqZ T x) = xuqZ T x :=
  hc_fix_down (one_le_two.trans (xuq_two_le_a T x)) (hcN_fix _ _)

section Z

variable {T : Ordinal.{0}} (hT : XuT T)
include hT

theorem xuqZ_eq {x : Ordinal.{0}} (hx : InE x) : xuqZ T x = hcN (xuqA T x) 0 := by
  unfold xuqZ; rw [max_eq_right (omega0_lt_inE hx).le]

theorem xuqZ_G1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : xuqZ T x < gq 1 x := by
  rw [xuqZ_eq hT hx]
  exact he_N_lt1 hx hx1 ((ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt
    (xuq_a_lt1 hT hx hx1)) (gm1_facts hx hx1).2.2.2.pos

/-- **Every bottom `φ(ℓ(x) + μ, 0)` (`μ < x`) of a band below `T` lies below the low field.** -/
theorem xuq_veb_lt_Z (B : XuqBd T) {x μ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.K.Λ.g < x)
    (hμx : μ < x) : veblen (B.K.Λ.l x + μ) 0 < xuqZ T x := by
  rw [xuqZ_eq hT hx, xl_N_eq]
  refine veblen_zero_lt_veblen_zero.2 (lt_of_lt_of_le ?_ (le_add_right le_rfl))
  exact (inE_indec (xuq_aE hT hx hx1)).add_lt (B.l_lt x hx hx1 hg) (hμx.trans (xuq_x_lt_a hT hx hx1))

/-! ## The bottom base of the level `L + κ` -/

/-- **THE BOTTOM BASE OF THE LEVEL `L + κ`** with the low field `xuqZ T`. -/
noncomputable def xuqBK (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) : XlB B.K.Λ κ where
  e := 0
  γN := max κ B.K.Λ.g
  Zo := xuqZ T
  lv := hκ
  lvN := le_max_left _ _
  lg := le_max_right _ _
  γN_lt := max_lt hκ B.K.Λ.g_lt
  G_lt := (xpBK B κ hκ).G_lt
  N_lt1 := (xpBK B κ hκ).N_lt1
  N_mem := (xpBK B κ hκ).N_mem
  N_cl := (xpBK B κ hκ).N_cl
  γN_cl := fun _ _ _ h hg => max_lt h hg
  Zo_fix := xuqZ_fix T
  Zo_G1 := fun _ hx hx1 => xuqZ_G1 hT hx hx1
  read := (xpBK B κ hκ).read
  N_pi := (xpBK B κ hκ).N_pi

theorem xuqBK_e (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) :
    (((xuqBK hT B κ hκ).e : ℕ) : Ordinal.{0}) = 0 := Nat.cast_zero

theorem xuqBK_γN (B : XpBd0) (κ : Ordinal.{0}) (hκ : κ < Om1) : (xuqBK hT B κ hκ).γN = max κ B.K.Λ.g := rfl

end Z

/-! ## Systems at the bottom `φ(L + κ, 0)` -/

/-- **`U` IS A SYSTEM AT THE BOTTOM `φ(L + κ, 0)` OF THE LEVEL `L + κ`** (gate `max κ g`, low field `xuqZ T`). -/
structure XuqAt (T : Ordinal.{0}) (Λ : HnLv) (κ : Ordinal.{0}) (U : HgVD) : Prop where
  B : U.B = veblen (Λ.L + κ) 0
  ix : U.ix = veblen (Λ.L + κ) 0
  γ : ∀ x, InE x → x < Om1 → (U.γ < x ↔ max κ Λ.g < x)
  b : ∀ x, InE x → x < Om1 → max κ Λ.g < x → U.b x = veblen (Λ.l x + κ) 0
  γ_le : U.γ ≤ max κ Λ.g
  Z : ∀ x, InE x → x < Om1 → U.Z x = if max κ Λ.g < x then evZ (veblen (Λ.l x + κ) 0) else xuqZ T x

section At

variable {T : Ordinal.{0}} (hT : XuT T)
include hT

/-- **A SYSTEM AT `φ(L + κ, 0)` STARTS THE BOTTOM RECURSION OF THE LEVEL `L + κ`.** -/
theorem xuq_start_of_at (B : XpBd0) {κ : Ordinal.{0}} (hκ : κ < Om1) {U : HgVD} (hU : XuqAt T B.K.Λ κ U) :
    XlStart (xuqBK hT B κ hκ) U where
  B := by rw [hU.B, xuqBK_e, add_zero]
  Zb := fun x hx hx1 => by
    rw [hU.Z x hx hx1]
    by_cases h : max κ B.K.Λ.g < x
    · rw [if_pos h, (xuqBK hT B κ hκ).Zl_eq hx h, xl_N_eq]
      have h2 : (2 : Ordinal.{0}) < B.K.Λ.l x + κ + 1 :=
        ((show (2 : Ordinal.{0}) ≤ ω from (by exact_mod_cast (natCast_lt_omega0 2).le)).trans
          (hnv_ωl B.K.Λ hx hx1).le).trans_lt (lt_add_one _)
      exact (hb_evZ_lt_fix2 (veblen_veblen_of_lt h2 0) (veblen_zero_lt_veblen_zero.2 (lt_add_one _))).le
    · rw [if_neg h, (xuqBK hT B κ hκ).Zl_low h]; rfl
  st := fun h2 hZ => by
    refine ⟨?_, fun x hx hx1 => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 => ?_⟩
    · show U.ix = veblen (B.K.Λ.L + κ) ((xuqBK hT B κ hκ).e + 0)
      rw [hU.ix, xuqBK_e, add_zero]
    · show U.γ < x ↔ max (max κ B.K.Λ.g) (U.g 0) < x
      rw [U.g_zero, max_eq_left zero_le]; exact hU.γ x hx hx1
    · have hκx : max κ B.K.Λ.g < x := (max_lt_iff.1 hg).1
      show U.b x = glA (B.K.Λ.l x + κ) (U.R 0 x) x
      rw [U.R_zero, (xuqBK hT B κ hκ).read hx hx1 hκx 0 (hcN_E _ _).pos, xuqBK_e, add_zero, hU.b x hx hx1 hκx]
    · rw [hU.Z x hx hx1]
      show _ = HgPB.Zst _ x
      by_cases h : max κ B.K.Λ.g < x
      · have hg : max (max κ B.K.Λ.g) (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_pos h, HgPB.Zst_eq _ hg]
        show evZ (veblen (B.K.Λ.l x + κ) 0) = evZ (glA (B.K.Λ.l x + κ) (U.R 0 x) x)
        rw [U.R_zero, (xuqBK hT B κ hκ).read hx hx1 h 0 (hcN_E _ _).pos, xuqBK_e, add_zero]
      · have hg : ¬ max (max κ B.K.Λ.g) (U.g 0) < x := by rw [U.g_zero, max_eq_left zero_le]; exact h
        rw [if_neg h, HgPB.Zst_low _ hg]
        show xuqZ T x = (xuqBK hT B κ hκ).Zl x
        rw [(xuqBK hT B κ hκ).Zl_low h]; rfl

/-- **THE TOP OF THE LEVEL `L + κ` IS A SYSTEM AT `φ(L + κ + 1, 0)`.** -/
theorem xuq_at_top (B : XpBd0) {κ : Ordinal.{0}} (hκ : κ < Om1) {U : HgVD} (hU : XuqAt T B.K.Λ κ U) :
    XuqAt T B.K.Λ (κ + 1) (xlTU (xpSt_spec B hκ) (xuq_start_of_at hT B hκ hU)) where
  B := by rw [xlTU_B, xl_N_eq, add_assoc]
  ix := by show hcN (B.K.Λ.L + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ := fun x hx _ => xp_max_succ hx
  b := fun x _ _ _ => by show hcN (B.K.Λ.l x + κ) 0 = _; rw [xl_N_eq, add_assoc]
  γ_le := by show max κ B.K.Λ.g ≤ max (κ + 1) B.K.Λ.g; exact max_le_max (lt_add_one κ).le le_rfl
  Z := fun x hx _ => by
    show (if max κ B.K.Λ.g < x then evZ (hcN (B.K.Λ.l x + κ) 0) else xuqZ T x) = _
    by_cases h : max κ B.K.Λ.g < x
    · rw [if_pos h, if_pos ((xp_max_succ hx).1 h), xl_N_eq, add_assoc]
    · rw [if_neg h, if_neg (fun h' => h ((xp_max_succ hx).2 h'))]

end At

end Googology.Trans.PoR.InaccPsi.R2.Xu
