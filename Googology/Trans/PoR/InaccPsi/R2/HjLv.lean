import Googology.Trans.PoR.InaccPsi.R2.HiVFr

/-!
# HjLv: A LEVEL DATUM `(L, ℓ)` (A MULTIPLE `L = Ω₁·q` READ AS `ℓ(x)`), AND THE LEVEL GATE AT `L + ν`

The levels of `Hi.HiVQ` / `Hi.HiVB` are `Ω₁ + ν` read as `x + ν`.  `HjLv` abstracts the prefix: a level datum is an
ordinal `L = Ω₁·q` with `Ω₁ ≤ L < G` (a code over every strongly critical `Z ≤ Ω₁`, in every hull `C(a, b)`) and a
reading `ℓ(x)` (`x ≤ ℓ(x)`, `ℓ(x) < Γ_{x+1}`, Lemma EXACT `π(ℓ(ρ)) = ℓ(σ)`).  The level `L + ν` is read as `ℓ(x) + ν`.

* `hj_opow_mul`, `hj_absorb_mul`, `hj_cl_mod` (**every code over `Z` is `Ω₁·q + r` with `r < Z`**);
* `HjLv`, `hjL1` (`L = Ω₁`, `ℓ(x) = x`), `HjLv.succ` (`L + Ω₁`, `ℓ(x) + x`);
* `hjv_cl_gate` (**THE LEVEL GATE at `L + ν`**: a code in `[φ(L+ν, j), φ(L+ν, j+1))` over `Z` has `ν < Z`), and
  the readings at the level `ℓ(x) + ν` (ports of the `Hi.hiv_*` lemmas, the prefix `x` replaced by `ℓ(x)`).

No new axiom.  New definitions: `HjLv`, `hjL1`, `HjLv.succ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hj

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
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Codes modulo `Ω₁` -/

theorem hj_Om_E : InE (Om (1 : Ordinal.{0})) := by rw [← Br.Om1_eq]; exact gl_Om1_E

/-- **A power `ω^e ≥ Ω₁` is a multiple of `Ω₁`.** -/
theorem hj_opow_mul {e : Ordinal.{0}} (h : Om 1 ≤ ω ^ e) : ∃ q, ω ^ e = Om 1 * q := by
  have hOE : ω ^ Om (1 : Ordinal.{0}) = Om 1 := hj_Om_E
  have he : Om 1 ≤ e := by
    rw [← hOE] at h
    exact (opow_le_opow_iff_right one_lt_omega0).1 h
  refine ⟨ω ^ (e - Om 1), ?_⟩
  conv_lhs => rw [← Ordinal.add_sub_cancel_of_le he]
  rw [opow_add, hOE]

/-- **`a + Ω₁·q = Ω₁·q`** for `a < Ω₁`, `q ≠ 0`. -/
theorem hj_absorb_mul {a q : Ordinal.{0}} (ha : a < Om 1) (hq : q ≠ 0) : a + Om 1 * q = Om 1 * q := by
  have h1 : 1 ≤ q := Order.one_le_iff_ne_zero.2 hq
  rw [← Ordinal.add_sub_cancel_of_le h1, mul_add, mul_one, ← add_assoc, Fp.fp_absorb hj_Om_E ha]

/-- **Every code over a strongly critical `Z ≤ Ω₁` is `Ω₁·q + r` with `r < Z`.** -/
theorem hj_cl_mod {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y) :
    ∃ q r, y = Om 1 * q + r ∧ r < Z := by
  induction hy with
  | small h => exact ⟨0, _, by rw [mul_zero, zero_add], h⟩
  | om => exact ⟨1, 0, by rw [mul_one, add_zero], hZ.1⟩
  | atom h =>
    rw [Set.mem_singleton_iff] at h
    subst h
    have hG : ω ^ gcG 0 = gcG 0 := gr_G_inE
    obtain ⟨q, hq⟩ := hj_opow_mul (show Om 1 ≤ ω ^ gcG 0 by rw [hG]; exact (gcG_Om1_lt 0).le)
    exact ⟨q, 0, by rw [add_zero, ← hq, hG], hZ.1⟩
  | @add u v hu hv ihu ihv =>
    obtain ⟨q1, r1, e1, hr1⟩ := ihu
    obtain ⟨q2, r2, e2, hr2⟩ := ihv
    rw [e1, e2]
    rcases eq_or_ne q2 0 with h0 | h0
    · refine ⟨q1, r1 + r2, ?_, hZ.isPrincipal hr1 hr2⟩
      rw [h0, mul_zero, zero_add, add_assoc]
    · refine ⟨q1 + q2, r2, ?_, hr2⟩
      rw [← add_assoc, add_assoc (Om 1 * q1), hj_absorb_mul (hr1.trans_le hZ1) h0, ← mul_add]
  | @phi c b hc hb _ _ =>
    by_cases hlt : veblen c b < Om 1
    · exact ⟨0, _, by rw [mul_zero, zero_add], he_cl_cnt hZ (GxCl.phi hc hb) hlt⟩
    · obtain ⟨e, he⟩ : ∃ e : Ordinal.{0}, veblen c b = ω ^ e := by
        rcases eq_or_ne c 0 with h | h
        · exact ⟨b, by rw [h, veblen_zero_apply]⟩
        · exact ⟨veblen c b, (gg_veblen_eps h).symm⟩
      rw [he] at hlt ⊢
      obtain ⟨q, hq⟩ := hj_opow_mul (not_lt.1 hlt)
      exact ⟨q, 0, by rw [add_zero, hq], hZ.1⟩

/-- **`Ω₁·q + r = Ω₁·q' + ν` with `r, ν < Ω₁` forces `r = ν`.** -/
theorem hj_mod_eq {q q' r ν : Ordinal.{0}} (hr : r < Om 1) (hν : ν < Om 1) (h : Om 1 * q + r = Om 1 * q' + ν) :
    r = ν := by
  have h2 := congrArg (· % Om 1) h
  simp only [mul_add_mod_self, mod_eq_of_lt hr, mod_eq_of_lt hν] at h2
  exact h2

/-! ## The level datum -/

/-- **A level datum**: a multiple `L = Ω₁·q`, `Ω₁ ≤ L < G`, a code in every hull, read as `ℓ(x)` with
`x ≤ ℓ(x)`, `ℓ(x) < Γ_{x+1}` and Lemma EXACT for `ℓ`. -/
structure HjLv where
  L : Ordinal.{0}
  l : Ordinal.{0} → Ordinal.{0}
  q : Ordinal.{0}
  OL : (Om1 : Ordinal.{0}) ≤ L
  L_G : L < gcG 0
  L_eq : L = Om 1 * q
  L_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), L ∈ S.CSet a b
  L_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} L
  l_ge : ∀ x, x ≤ l x
  l_lt : ∀ x, InE x → x < Om1 → l x < lgG x
  l_pi : ∀ σ ρ, Bases σ ρ → l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ

/-- **The level datum `Ω₁`, read as `x`.** -/
noncomputable def hjL1 : HjLv where
  L := Om1
  l := fun x => x
  q := 1
  OL := le_rfl
  L_G := hg_Om1_lt_G 0
  L_eq := by rw [mul_one, Br.Om1_eq]
  L_mem := fun _ _ _ => by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  L_code := fun _ _ _ => by rw [Br.Om1_eq]; exact GxCl.om
  l_ge := fun _ => le_rfl
  l_lt := fun _ hx hx1 => (lgG_facts hx hx1).2.1
  l_pi := fun _ _ hB => pi_base hB

namespace HjLv

variable (Λ : HjLv)

theorem L_lt (α : Ordinal.{0}) : Λ.L < gcG α := by
  rcases eq_or_ne α 0 with h | h
  · rw [h]; exact Λ.L_G
  · exact Λ.L_G.trans (gcG_lt (pos_iff_ne_zero.2 h))

/-- **The next level datum `L + Ω₁`, read as `ℓ(x) + x`.** -/
noncomputable def succ : HjLv where
  L := Λ.L + Om1
  l := fun x => Λ.l x + x
  q := Λ.q + 1
  OL := Λ.OL.trans le_self_add
  L_G := (inE_indec gr_G_inE).add_lt Λ.L_G (hg_Om1_lt_G 0)
  L_eq := by rw [mul_add, mul_one, ← Λ.L_eq, Br.Om1_eq]
  L_mem := fun S a b => CSet.add_mem (Λ.L_mem S a b) (by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _))
  L_code := fun Z hZ hZ1 => GxCl.add (Λ.L_code Z hZ hZ1) (by rw [Br.Om1_eq]; exact GxCl.om)
  l_ge := fun x => (Λ.l_ge x).trans le_self_add
  l_lt := fun x hx hx1 => (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (Λ.l_lt x hx hx1) (lgG_facts hx hx1).2.1
  l_pi := fun σ ρ hB => by
    obtain ⟨l1, l2⟩ := Λ.l_pi σ ρ hB
    obtain ⟨r1, r2⟩ := pi_base hB
    obtain ⟨u1, u2⟩ := pi_add hB l1 r1
    rw [l2, r2] at u2
    exact ⟨u1, u2⟩

theorem succ_L : Λ.succ.L = Λ.L + Om1 := rfl

theorem succ_l (x : Ordinal.{0}) : Λ.succ.l x = Λ.l x + x := rfl

end HjLv

/-! ## The level gate at `L + ν` -/

theorem hjv_L1 (Λ : HjLv) (ν : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ Λ.L + ν :=
  (hg_one_lt_Om1.le.trans Λ.OL).trans le_self_add

theorem hjv_L0 (Λ : HjLv) (ν : Ordinal.{0}) : Λ.L + ν ≠ 0 := (zero_lt_one.trans_le (hjv_L1 Λ ν)).ne'

theorem hjv_ωL (Λ : HjLv) (ν : Ordinal.{0}) : ω < Λ.L + ν :=
  ((omega0_lt_inE gl_Om1_E).trans_le Λ.OL).trans_le le_self_add

/-- **THE LEVEL GATE**: a code over a strongly critical `Z ≤ Ω₁` in `[φ(L+ν, j), φ(L+ν, j+1))` (`ν < Ω₁`, `j` not a
fixed point, `G < φ(L+ν, j)`) has `ν < Z`. -/
theorem hjv_cl_gate (Λ : HjLv) {ν : Ordinal.{0}} (hν : ν < Om1) {Z j : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1)
    (hj : j < veblen (Λ.L + ν) j) (hGQ : gcG 0 < veblen (Λ.L + ν) j) {y : Ordinal.{0}} (hy : GxCl Z {gcG 0} y)
    (hQy : veblen (Λ.L + ν) j ≤ y) (hyZ : y < veblen (Λ.L + ν) (j + 1)) : ν < Z := by
  have h := hi_cl_lvl (hjv_L1 Λ ν) hZ1 hj hGQ hy hQy hyZ
  obtain ⟨q, r, he, hr⟩ := hj_cl_mod hZ hZ1 h
  rw [Λ.L_eq] at he
  rw [Br.Om1_eq] at hν
  rw [← hj_mod_eq (hr.trans_le hZ1) hν he.symm]
  exact hr

theorem hjv_L_code (Λ : HjLv) {ν Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hνZ : ν < Z) :
    GxCl Z {gcG 0} (Λ.L + ν) :=
  GxCl.add (Λ.L_code Z hZ hZ1) (GxCl.small hνZ)

theorem hjv_L_mem (Λ : HjLv) (S : InaccSeq.{0}) {ν a b : Ordinal.{0}} (hνb : ν < b) : Λ.L + ν ∈ S.CSet a b :=
  CSet.add_mem (Λ.L_mem S a b) (CSet.of_lt hνb)

theorem hjv_fixk (Λ : HjLv) {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) (k : ℕ) :
    veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (hjv_ωL Λ ν)) a

theorem hjv_Lω (Λ : HjLv) {ν v : Ordinal.{0}} (hv : LuP (Λ.L + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (hjv_ωL Λ ν) a

/-! ## The readings at the level `ℓ(x) + ν` -/

section Base

variable (Λ : HjLv) {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hjv_ωl : ω < Λ.l x + ν := ((omega0_lt_inE hx).trans_le (Λ.l_ge x)).trans_le le_self_add

theorem hjv_xl : x ≤ Λ.l x + ν := (Λ.l_ge x).trans le_self_add

theorem hjv_rfixk {v : Ordinal.{0}} (hv : LuP (Λ.l x + ν) v) (k : ℕ) : veblen (k : Ordinal.{0}) v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt ((natCast_lt_omega0 k).trans (hjv_ωl Λ hx hx1)) a

theorem hjv_rfixω {v : Ordinal.{0}} (hv : LuP (Λ.l x + ν) v) : veblen ω v = v := by
  obtain ⟨a, rfl⟩ := hv
  exact veblen_veblen_of_lt (hjv_ωl Λ hx hx1) a

variable (hνx : ν < x)
include hνx

theorem hjv_G : Λ.l x + ν < lgG x :=
  (inE_indec (lgG_facts hx hx1).2.2.2.1).add_lt (Λ.l_lt x hx hx1) (hνx.trans (lgG_facts hx hx1).2.1)

theorem hjv_G1 : Λ.l x + ν + 1 < lgG x :=
  (ev_isSuccLimit_of_inE (lgG_facts hx hx1).2.2.2.1).add_one_lt (hjv_G Λ hx hx1 hνx)

theorem hjv_q : Λ.l x + ν < gq 1 x := (hjv_G Λ hx hx1 hνx).trans (mg_lgG_lt_G1 hx hx1)

theorem hjv_T : Λ.l x + ν ∈ Tset x ∧ Λ.l x + ν < Om1 := gm1_T hx hx1 (hjv_q Λ hx hx1 hνx)

theorem hjv_one : (1 : Ordinal.{0}) ≤ Λ.l x + ν := (hi_one_le hx hx1).trans (hjv_xl Λ hx hx1)

theorem hjv_glA_P {t : Ordinal.{0}} (ht : t < gq 1 x) : LuP (Λ.l x + ν) (glA (Λ.l x + ν) t x) := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hjv_T Λ hx hx1 hνx
  exact glA_P hx hx1 (hjv_one Λ hx hx1 hνx) hT h1 htT ht1

theorem hjv_glA_facts {t : Ordinal.{0}} (ht : t < gq 1 x) :
    Λ.l x + ν < glA (Λ.l x + ν) t x ∧ glA (Λ.l x + ν) t x < Om1 ∧ t < glA (Λ.l x + ν) t x := by
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht
  obtain ⟨hT, h1⟩ := hjv_T Λ hx hx1 hνx
  obtain ⟨-, -, ha1, -, hβa, hta⟩ := glA_facts hx hx1 (hjv_one Λ hx hx1 hνx) hT h1 htT ht1
  exact ⟨hβa, ha1, hta⟩

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + t + 1) = hdNx (ℓ(x)+ν) (ϑˣ(Ω₁·(ℓ(x)+ν) + t))`.** -/
theorem hjv_glA_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) :
    glA (Λ.l x + ν) (t + 1) x = hdNx (Λ.l x + ν) (glA (Λ.l x + ν) t x) := by
  obtain ⟨i, hi⟩ := hjv_glA_P Λ hx hx1 hνx ((lt_add_one t).trans ht)
  rw [hc_glA_succV hx hx1 (hjv_one Λ hx hx1 hνx) (hjv_q Λ hx hx1 hνx) ht hi.symm, ← hdNx_veb, hi]

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + P) = hdNx (ℓ(x)+ν) P`** at a fixed point `P ∈ (ℓ(x)+ν, Γ_{x+2})` of `φ(ℓ(x)+ν, ·)`. -/
theorem hjv_glA_fixP {P : Ordinal.{0}} (hP : veblen (Λ.l x + ν) P = P) (hxP : Λ.l x + ν < P) (hPq : P < gq 1 x) :
    glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P := by
  rw [hdNx_fixP hP]
  exact hc_glA_fixG hx hx1 (hjv_one Λ hx hx1 hνx) (hjv_q Λ hx hx1 hνx) hP hxP ((hjv_xl Λ hx hx1).trans_lt hxP) hPq

/-- **THE CLOSED FORM BELOW `N_{ℓ(x)+ν}(P)`**. -/
theorem hjv_lvglAV {P r i0 : Ordinal.{0}} (hP0 : glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (Λ.l x + ν) P < gq 1 x) (hi0 : veblen (Λ.l x + ν) i0 = hdNx (Λ.l x + ν) P)
    (hr : r < hcN (Λ.l x + ν) P) : glA (Λ.l x + ν) (P + r) x = veblen (Λ.l x + ν) (i0 + r) := by
  have hNE := hcN_E (Λ.l x + ν) P
  have hSN : hdNx (Λ.l x + ν) P < hcN (Λ.l x + ν) P := hdNx_lt_N (hcN_gt (Λ.l x + ν) P)
  have hi0H : i0 < hcN (Λ.l x + ν) P := (right_le_veblen (Λ.l x + ν) i0).trans_lt (by rw [hi0]; exact hSN)
  have hir : i0 + r < hcN (Λ.l x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have hlt : veblen (Λ.l x + ν) (i0 + r) < hcN (Λ.l x + ν) P := by
    have := (isNormal_veblen (Λ.l x + ν)).strictMono hir; rwa [hcN_fix] at this
  have hrq : P + r < gq 1 x := (inE_indec (gm1_facts hx hx1).2.2.2).add_lt hPq (hr.trans hNq)
  have hPi : P < veblen (Λ.l x + ν) i0 := by rw [hi0]; exact hdNx_gt (Λ.l x + ν) P
  exact hc_glAV hx hx1 (hjv_one Λ hx hx1 hνx) (hjv_q Λ hx hx1 hνx) hPq (by rw [hP0, hi0]) r hrq (fun ν' h' _ =>
    hc_nofixG hPi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hlt))

/-- **`ϑˣ(Ω₁·(ℓ(x)+ν) + P + r) < N_{ℓ(x)+ν}(P)`** for `r < N_{ℓ(x)+ν}(P)`. -/
theorem hjv_glA_lt {P r : Ordinal.{0}} (hP0 : glA (Λ.l x + ν) P x = hdNx (Λ.l x + ν) P) (hPq : P < gq 1 x)
    (hNq : hcN (Λ.l x + ν) P < gq 1 x) (hr : r < hcN (Λ.l x + ν) P) :
    glA (Λ.l x + ν) (P + r) x < hcN (Λ.l x + ν) P := by
  obtain ⟨i0, hi0⟩ := hdNx_LuP (Λ.l x + ν) P
  rw [hjv_lvglAV Λ hx hx1 hνx hP0 hPq hNq hi0 hr]
  have hNE := hcN_E (Λ.l x + ν) P
  have hi0H : i0 < hcN (Λ.l x + ν) P :=
    (right_le_veblen (Λ.l x + ν) i0).trans_lt (by rw [hi0]; exact hdNx_lt_N (hcN_gt (Λ.l x + ν) P))
  have hir : i0 + r < hcN (Λ.l x + ν) P := (inE_indec hNE).add_lt hi0H hr
  have := (isNormal_veblen (Λ.l x + ν)).strictMono hir; rwa [hcN_fix] at this

/-- **`N_{ℓ(x)+ν}(P) = ϑˣ(Ω₁·(ℓ(x)+ν+1) + P)`** at a fixed point `P ∈ (ℓ(x)+ν, Γ_{x+2})` of `φ(ℓ(x)+ν+1, ·)`. -/
theorem hjv_N_glA {P : Ordinal.{0}} (hP : veblen (Λ.l x + ν + 1) P = P) (hxP : Λ.l x + ν + 1 < P)
    (hPq : P < gq 1 x) : hcN (Λ.l x + ν) P = glA (Λ.l x + ν + 1) P x := by
  have hq1 : Λ.l x + ν + 1 < gq 1 x :=
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (hjv_q Λ hx hx1 hνx)
  have e : hcN (Λ.l x + ν) P = veblen (Λ.l x + ν + 1) (P + 1) := by
    have := hcN_veb (Λ.l x + ν) P; rwa [hP] at this
  rw [e, hc_glA_fixG hx hx1 ((hjv_one Λ hx hx1 hνx).trans le_self_add) hq1 hP hxP
    (((hjv_xl Λ hx hx1).trans le_self_add).trans_lt hxP) hPq]

end Base

/-- **Lemma EXACT for `ϑᵖ(Ω₁·(ℓ(ρ)+ν) + t)`**: `π(ϑᵖ(Ω₁·(ℓ(ρ)+ν) + t)) = ϑ^σ(Ω₁·(ℓ(σ)+ν) + π(t))` (`ν < σ`). -/
theorem hjv_glA_pi (Λ : HjLv) {ν σ ρ t : Ordinal.{0}} (hB : Bases σ ρ) (hνσ : ν < σ) (ht : t ∈ TB ρ σ)
    (htq : t < gq 1 ρ) :
    glA (Λ.l ρ + ν) t ρ ∈ TB ρ σ ∧ pi σ ρ (glA (Λ.l ρ + ν) t ρ) = glA (Λ.l σ + ν) (pi σ ρ t) σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨r1, r2⟩ := Λ.l_pi σ ρ hB
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h := glA_pi hB u1 (hjv_T Λ hB.2.1 hρ1 (hνσ.trans hB.2.2.1)).2 ht (gm1_T hB.2.1 hρ1 htq).2
  rw [u2] at h
  exact h

/-- **Lemma EXACT for `ℓ(ρ) + ν + 1`**. -/
theorem hjv_lev1_pi (Λ : HjLv) {ν σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hνσ : ν < σ) :
    Λ.l ρ + ν + 1 ∈ TB ρ σ ∧ pi σ ρ (Λ.l ρ + ν + 1) = Λ.l σ + ν + 1 := by
  obtain ⟨r1, r2⟩ := Λ.l_pi σ ρ hB
  obtain ⟨u1, u2⟩ := pi_add hB r1 (mem_TB_of_lt hB hνσ)
  rw [r2, pi_lt hB hνσ] at u2
  have h1σ : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  obtain ⟨w1, w2⟩ := pi_add hB u1 (mem_TB_of_lt hB h1σ)
  rw [u2, pi_lt hB h1σ] at w2
  exact ⟨w1, w2⟩

end Googology.Trans.PoR.InaccPsi.R2.Hj
