import Googology.Trans.PoR.InaccPsi.R2.WoArith

/-!
# WoDat: RAW BASE DATA, GOOD UP TO A LEVEL; THE TWO-GATE BASE AT EVERY LOWER LEVEL; THE SHAPE OF A SYSTEM

A RAW DATUM `r = (F, F(x), γ, Z_o)` (no proofs, `WoR`) is GOOD UP TO THE LEVEL `ℓ` (`WoGood r ℓ`) when `F` is a value
of `φ(ℓ, ·)`, the reading `F(x)` is a value of `φ(rdc μ x, ·)` above `max γ (gtc μ)` for every level `μ ≤ ℓ`, and the
code-gate, membership and Lemma EXACT facts hold.  The two instances: `G` at every level (`woG`, `woGood_G`) and every
pseudo-base of a level (`woQR`, `woGood_Q`).  A good datum gives:

* `woWB r μ` (**THE TWO-GATE BASE OF EVERY LEVEL `μ` WITH `μ + Ω₁ ≤ ℓ`**: an `Hn.HnWB (whLv μ)`, code gate `γ`,
  reading gate `max γ (gtc μ)`; it depends only on the data of `r`);
* `woQ1 r` (**the datum as a pseudo-base of the level `Ω₁ + 0`**: an `Hn.HnVQ Hn.hnL1 0`);
* `WoSh r ℓ S` (**THE SHAPE OF A SYSTEM AT THE LEVEL `ℓ` OVER `r`**: bound `hdNx ℓ F`, base gate between `γ` and
  `max γ (gtc ℓ)` and cut like it, base reading `hdNx (rdc ℓ x) (F(x))`, bound field, high condition),
  `woSh_W` (a shape at `μ` is a start over `woWB r μ`), `woSh_succ` (**the union `Hn.hnwU` over `woWB r μ` has the
  shape at `μ + Ω₁`**).

No new axiom.  New definitions: `WoR`, `WoGood`, `woLv`, `woWB`, `woQ1`, `WoSh`, `woG`, `woQR`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wo

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

/-! ## Level arithmetic -/

/-- **A level is a limit**: `μ < ℓ` ⇒ `μ + 1 < ℓ`. -/
theorem wo_lev_lim {ℓ μ : Ordinal.{0}} (hℓ : WmLev ℓ) (h : μ < ℓ) : μ + 1 < ℓ := by
  obtain ⟨k, hk⟩ := hℓ.2.1
  rw [hk] at h ⊢
  have hq : μ / Om1 < k := (Ordinal.div_lt wh_Om1_pos.ne').2 h
  have hl : IsSuccLimit (Om1 * (μ / Om1) + Om1) := Ordinal.isSuccLimit_add _ gl_Om1_lim
  calc μ + 1 < Om1 * (μ / Om1) + Om1 := hl.add_one_lt (lt_mul_div_add μ wh_Om1_pos.ne')
  _ = Om1 * (μ / Om1 + 1) := by rw [mul_add_one]
  _ ≤ Om1 * k := mul_le_mul_left' (Order.add_one_le_of_lt hq) _

theorem wo_lev_W {μ : Ordinal.{0}} (h : WmLev μ) : μ < gfE := h.2.2

/-- The successor of a level below a level. -/
theorem wo_lev_succ {μ ℓ : Ordinal.{0}} (hμ : WmLev μ) (hℓ : WmLev ℓ) (h : μ + Om1 ≤ ℓ) : WmLev (μ + Om1) :=
  ⟨hμ.1.trans le_self_add, dvd_add hμ.2.1 (dvd_refl _), h.trans_lt hℓ.2.2⟩

/-- **The gates of `μ` and `μ + Ω₁` have the same `ε`-cut.** -/
theorem wo_gtc_succ_iff {μ x : Ordinal.{0}} (hμ : WmLev μ) (hx : InE x) : gtc (μ + Om1) < x ↔ gtc μ < x :=
  ⟨fun h => ((wh_rdc_add_Om1 μ hμ.2.2 hμ.2.1 0).2).trans_lt h, fun h => wh_gtc_add_Om1_ltE hx hμ.2.2 h⟩

/-- **The reading of `μ + Ω₁`** above the gate of `μ`. -/
theorem wo_rdc_succ {μ : Ordinal.{0}} (hμ : WmLev μ) (x : Ordinal.{0}) : rdc (μ + Om1) x = rdc μ x + x :=
  (wh_rdc_add_Om1 μ hμ.2.2 hμ.2.1 x).1

/-- The level datum of a level. -/
noncomputable abbrev woLv (μ : Ordinal.{0}) (h : WmLev μ) : HnLv := whLv μ h.1 h.2.1 h.2.2

theorem woLv_l {μ x : Ordinal.{0}} (h : WmLev μ) (hx : InE x) (hg : gtc μ < x) : (woLv μ h).l x = rdc μ x :=
  whLv_l h.1 h.2.1 h.2.2 hx hg

/-- **`hdNx μ F < hdNx ℓ F`** for `F` a value of `φ(ℓ, ·)` and `μ < ℓ`. -/
theorem wo_N_lt {μ ℓ F : Ordinal.{0}} (hℓ : WmLev ℓ) (hF : LuP ℓ F) (h : μ < ℓ) : hdNx μ F < hdNx ℓ F :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx (wo_lev_lim hℓ h))

theorem wo_fix_of_LuP {μ ℓ F : Ordinal.{0}} (hF : LuP ℓ F) (h : μ < ℓ) : veblen μ F = F := by
  obtain ⟨a, ha⟩ := hF; rw [← ha]; exact veblen_veblen_of_lt h a

/-! ## Raw data -/

/-- **A RAW BASE DATUM**: a point, a reading, a code gate, an outer low field. -/
structure WoR where
  F : Ordinal.{0}
  Fr : Ordinal.{0} → Ordinal.{0}
  γ : Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}

/-- **A RAW DATUM GOOD UP TO THE LEVEL `ℓ`.** -/
structure WoGood (r : WoR) (ℓ : Ordinal.{0}) : Prop where
  lev : WmLev ℓ
  γ_lt : r.γ < Om1
  F_P : LuP ℓ r.F
  G_le : gcG 0 ≤ r.F
  S_lt1 : hdNx ℓ r.F < gcG 1
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → r.γ < b → r.F ∈ S.CSet a b
  S_mem : ∀ μ, WmLev μ → μ ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a → max r.γ (gtc μ) < b →
    hdNx μ r.F ∈ S.CSet a b
  S_memW : ∀ μ, WmLev μ → μ + Om1 ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, 0 < a →
    max r.γ (gtc μ) < b → hdNx (μ + Om1) r.F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → r.F ≤ y → y < hdNx ℓ r.F →
    GxCl Z {gcG 0} r.F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → r.F ≤ y → y < hdNx ℓ r.F → r.γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (hdNx ℓ r.F) → r.γ < Z
  rd : ∀ μ, WmLev μ → μ ≤ ℓ → ∀ x, InE x → x < Om1 → max r.γ (gtc μ) < x →
    LuP (rdc μ x) (r.Fr x) ∧ rdc μ x < r.Fr x ∧ hdNx (rdc μ x) (r.Fr x) < r.Zo x
  S_pi : ∀ μ, WmLev μ → μ ≤ ℓ → ∀ σ ρ, Bases σ ρ → max r.γ (gtc μ) < σ →
    hdNx (rdc μ ρ) (r.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (rdc μ ρ) (r.Fr ρ)) = hdNx (rdc μ σ) (r.Fr σ)
  Zo_fix : ∀ x, veblen 2 (r.Zo x) = r.Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → r.Zo x < gq 1 x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → r.γ < σ → r.Fr ρ ∈ TB ρ σ ∧ pi σ ρ (r.Fr ρ) = r.Fr σ

namespace WoGood

variable {r : WoR} {ℓ : Ordinal.{0}} (h : WoGood r ℓ)
include h

/-- **GOOD UP TO `ℓ` ⇒ GOOD UP TO EVERY LOWER LEVEL.** -/
theorem mono {μ : Ordinal.{0}} (hμ : WmLev μ) (hle : μ ≤ ℓ) : WoGood r μ where
  lev := hμ
  γ_lt := h.γ_lt
  F_P := hd_LuP_mono hle h.F_P
  G_le := h.G_le
  S_lt1 := (hdNx_mono hle _).trans_lt h.S_lt1
  F_mem := h.F_mem
  S_mem := fun ν hν hνμ => h.S_mem ν hν (hνμ.trans hle)
  S_memW := fun ν hν hνμ => h.S_memW ν hν (hνμ.trans hle)
  F_code := fun Z hZ hZ1 y hy hQy hyZ => h.F_code Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hle _))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => h.F_cl Z hZ hZ1 y hy hQy (hyZ.trans_le (hdNx_mono hle _))
  S_cl := fun Z hZ hZ1 hc => by
    rcases hle.lt_or_eq with hlt | rfl
    · exact h.F_cl Z hZ hZ1 _ hc (hdNx_gt _ _).le (wo_N_lt h.lev h.F_P hlt)
    · exact h.S_cl Z hZ hZ1 hc
  rd := fun ν hν hνμ => h.rd ν hν (hνμ.trans hle)
  S_pi := fun ν hν hνμ => h.S_pi ν hν (hνμ.trans hle)
  Zo_fix := h.Zo_fix
  Zo_G1 := h.Zo_G1
  Fr_pi := h.Fr_pi

section Base

variable {μ x : Ordinal.{0}} (hμ : WmLev μ) (hμℓ : μ + Om1 ≤ ℓ) (hx : InE x) (hx1 : x < Om1)
  (hg : max r.γ (gtc μ) < x)
include hμ hμℓ hx hx1 hg

theorem rdS : max r.γ (gtc (μ + Om1)) < x :=
  max_lt (max_lt_iff.1 hg).1 ((wo_gtc_succ_iff hμ hx).2 (max_lt_iff.1 hg).2)

/-- `F(x)` is a value of `φ(rdc μ x + x, ·)`. -/
theorem rP : LuP (rdc μ x + x) (r.Fr x) := by
  have := (h.rd _ (wo_lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).1
  rwa [wo_rdc_succ hμ] at this

theorem rgt : rdc μ x + x < r.Fr x := by
  have := (h.rd _ (wo_lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).2.1
  rwa [wo_rdc_succ hμ] at this

theorem rZo : hdNx (rdc μ x + x) (r.Fr x) < r.Zo x := by
  have := (h.rd _ (wo_lev_succ hμ h.lev hμℓ) hμℓ x hx hx1 (rdS h hμ hμℓ hx hx1 hg)).2.2
  rwa [wo_rdc_succ hμ] at this

/-- **`F(x)` is a fixed point of `φ(rdc μ x, ·)`.** -/
theorem rfix : veblen (rdc μ x) (r.Fr x) = r.Fr x :=
  wo_fix_of_LuP (rP h hμ hμℓ hx hx1 hg) (lt_add_of_pos_right _ hx.pos)

theorem rlt1 : r.Fr x < gq 1 x :=
  ((hdNx_gt _ _).trans (rZo h hμ hμℓ hx hx1 hg)).trans (h.Zo_G1 x hx hx1)

end Base

end WoGood

/-! ## The two-gate base at a lower level -/

/-- **THE TWO-GATE BASE OF THE LEVEL `μ`** (`μ + Ω₁ ≤ ℓ`): point `F`, reading `F(x)`, code gate `γ`, reading gate
`max γ (gtc μ)`, outer low field `Z_o`. -/
noncomputable def woWB (r : WoR) (μ : Ordinal.{0}) (hμ : WmLev μ) (h : WoGood r (μ + Om1)) : HnWB (woLv μ hμ) where
  F := r.F
  Fr := r.Fr
  γ := r.γ
  γR := max r.γ (gtc μ)
  Zo := r.Zo
  γ_lt := h.γ_lt
  γR_lt := max_lt h.γ_lt (gtc_lt_Om1 μ hμ.2.2)
  γ_le := le_max_left _ _
  lg := le_max_right _ _
  γR_cl := fun _ _ _ h1 h2 => max_lt h1 h2
  F_P := h.F_P
  G_le := h.G_le
  S_lt1 := h.S_lt1
  F_mem := h.F_mem
  S_mem := fun S _ _ ha hb => h.S_memW μ hμ le_rfl S ha hb
  F_code := h.F_code
  F_cl := h.F_cl
  S_cl := h.S_cl
  Fr_gt := fun hx hx1 hγ => by
    show whRd μ _ + _ < _
    rw [whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rgt hμ le_rfl hx hx1 hγ
  Fr_P := fun hx hx1 hγ => by
    show LuP (whRd μ _ + _) _
    rw [whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rP hμ le_rfl hx hx1 hγ
  S_Zo := fun hx hx1 hγ => by
    show hdNx (whRd μ _ + _) _ < _
    rw [whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hγ).2]; exact h.rZo hμ le_rfl hx hx1 hγ
  Zo_fix := h.Zo_fix
  Zo_G1 := h.Zo_G1
  Fr_pi := fun hB hγ => h.Fr_pi hB ((le_max_left _ _).trans_lt hγ)
  S_pi := fun {σ ρ} hB hγ => by
    show hdNx (whRd μ ρ + ρ) _ ∈ _ ∧ pi σ ρ (hdNx (whRd μ ρ + ρ) _) = hdNx (whRd μ σ + σ) _
    have hσg : gtc μ < σ := (max_lt_iff.1 hγ).2
    rw [whRd_eq hB.2.1 hμ.1 hμ.2.2 (hσg.trans hB.2.2.1), whRd_eq hB.1 hμ.1 hμ.2.2 hσg,
      ← wo_rdc_succ hμ, ← wo_rdc_succ hμ]
    exact h.S_pi _ (wo_lev_succ hμ h.lev le_rfl) le_rfl σ ρ hB (h.rdS hμ le_rfl hB.1 (hB.2.2.1.trans hB.2.2.2) hγ)

theorem woWB_γR (r : WoR) (μ : Ordinal.{0}) (hμ : WmLev μ) (h : WoGood r (μ + Om1)) :
    (woWB r μ hμ h).γR = max r.γ (gtc μ) := rfl

/-! ## The shape of a system -/

/-- **THE SHAPE OF A SYSTEM AT THE LEVEL `ℓ` OVER `r`.** -/
def WoSh (r : WoR) (ℓ : Ordinal.{0}) (S : HgVD) : Prop :=
  S.B = hdNx ℓ r.F ∧ (r.γ ≤ S.γ ∧ S.γ ≤ max r.γ (gtc ℓ)) ∧
    (∀ x, InE x → x < Om1 → (S.γ < x ↔ max r.γ (gtc ℓ) < x)) ∧
    (∀ x, InE x → x < Om1 → max r.γ (gtc ℓ) < x → S.b x = hdNx (rdc ℓ x) (r.Fr x)) ∧
    (∀ x, InE x → x < Om1 → S.Z x = if max r.γ (gtc ℓ) < x then evZ (hdNx (rdc ℓ x) (r.Fr x)) else r.Zo x) ∧
    ∀ c σ, r.F ≤ c → c < S.B → InE σ → σ < Om1 → S.g c < σ → r.γ < σ

/-- **A SHAPE AT `μ` IS A START OVER `woWB r μ`.** -/
theorem woSh_W {r : WoR} {μ : Ordinal.{0}} (hμ : WmLev μ) (h : WoGood r (μ + Om1)) {S : HgVD}
    (hS : WoSh r μ S) : HnWShape (woWB r μ hμ h) 0 S := by
  obtain ⟨hB, -, hγ, hb, hZ, hhi⟩ := hS
  have hmx : ∀ x : Ordinal.{0}, max (max r.γ (gtc μ)) 0 < x ↔ max r.γ (gtc μ) < x := fun x => by
    rw [max_eq_left zero_le]
  refine ⟨?_, fun x hx hx1 => ?_, fun x hx hx1 hk => ?_, fun x hx hx1 => ?_, hhi⟩
  · rw [hB]; show hdNx μ r.F = veblen (μ + 0) (r.F + 1)
    rw [add_zero]; exact hdNx_fixP (wo_fix_of_LuP h.F_P (lt_add_of_pos_right _ wh_Om1_pos))
  · rw [hγ x hx hx1]; exact (hmx x).symm
  · have hk' := (hmx x).1 hk
    rw [hb x hx hx1 hk']
    show hdNx (rdc μ x) (r.Fr x) = veblen (whRd μ x + 0) (r.Fr x + 1)
    rw [add_zero, whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hk').2]
    exact hdNx_fixP (h.rfix hμ le_rfl hx hx1 hk')
  · rw [hZ x hx hx1]
    show _ = if max (max r.γ (gtc μ)) 0 < x then evZ (veblen (whRd μ x + 0) (r.Fr x + 1))
      else (woWB r μ hμ h).hnwZo x
    by_cases hk : max r.γ (gtc μ) < x
    · rw [if_pos hk, if_pos ((hmx x).2 hk), add_zero, whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hk).2,
        hdNx_fixP (h.rfix hμ le_rfl hx hx1 hk)]
    · rw [if_neg hk, if_neg (fun h' => hk ((hmx x).1 h')), (woWB r μ hμ h).hnwZo_low hk]
      rfl

/-- **THE UNION OVER `woWB r μ` HAS THE SHAPE AT `μ + Ω₁`.** -/
theorem woSh_succ {r : WoR} {μ : Ordinal.{0}} (hμ : WmLev μ) (h : WoGood r (μ + Om1))
    (St0 : HnVStTy (woLv μ hμ) 0) (h0 : ∀ Q U h, HnVSpec Q U (St0 Q U h)) {S : HgVD} (hS : WoSh r μ S) :
    WoSh r (μ + Om1) (hnwU (woWB r μ hμ h) St0 h0 S (woSh_W hμ h hS)) := by
  set P := woWB r μ hμ h
  have hcut : ∀ x, InE x → (max r.γ (gtc μ) < x ↔ max r.γ (gtc (μ + Om1)) < x) := fun x hx => by
    rw [max_lt_iff, max_lt_iff, wo_gtc_succ_iff hμ hx]
  have hgl : gtc μ ≤ gtc (μ + Om1) := (wh_rdc_add_Om1 μ hμ.2.2 hμ.2.1 0).2
  refine ⟨rfl, ⟨le_max_left _ _, max_le_max le_rfl hgl⟩, fun x hx _ => hcut x hx, fun x hx hx1 hk => ?_,
    fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · have hk' := (hcut x hx).2 hk
    show hdNx (whRd μ x + x) (r.Fr x) = _
    rw [whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hk').2, wo_rdc_succ hμ]
  · show hnwUZ P x = _
    unfold hnwUZ
    by_cases hk : max r.γ (gtc μ) < x
    · rw [if_pos (show P.γR < x from hk), if_pos ((hcut x hx).1 hk)]
      show evZ (hdNx (whRd μ x + x) (r.Fr x)) = _
      rw [whRd_eq hx hμ.1 hμ.2.2 (max_lt_iff.1 hk).2, wo_rdc_succ hμ]
    · rw [if_neg (show ¬ P.γR < x from hk), if_neg (fun h' => hk ((hcut x hx).2 h'))]
      rfl
  · by_cases hSc : S.B ≤ c
    · exact (le_max_left _ _).trans_lt (hnwU_highR P St0 h0 S (woSh_W hμ h hS) hSc hc hσ hσ1 hg)
    · have hc0 : c < S.B := not_le.1 hSc
      rw [hnwU_g0 P St0 h0 S (woSh_W hμ h hS) hc0] at hg
      exact hS.2.2.2.2.2 c σ hFc hc0 hσ hσ1 hg

/-! ## The instance `G` -/

/-- **`G` as a raw datum**: point `G`, reading `Γ_{x+1}`, code gate `0`, outer low field `φ(ε_{x+1}, Γ_{x+1}+1)`. -/
noncomputable def woG : WoR := ⟨gcG 0, lgG, 0, whZo⟩

theorem wo_G_fix {μ : Ordinal.{0}} (hμ : WmLev μ) : veblen μ (gcG 0) = gcG 0 :=
  gn_veb_fix (gcG_SC 0) (hμ.2.2.trans gfE_lt_G0)

theorem wo_one_le_rdc {μ x : Ordinal.{0}} (hμ : WmLev μ) (hx : InE x) : (1 : Ordinal.{0}) ≤ rdc μ x :=
  (one_lt_omega0.trans (omega0_lt_inE hx)).le.trans (wh_le_rdc hx hμ.1 hμ.2.2)

theorem wo_rdc_lt_lgG {μ x : Ordinal.{0}} (hμ : WmLev μ) (hx : InE x) (hx1 : x < Om1) (hg : gtc μ < x) :
    rdc μ x < lgG x := (rdc_lt_eN hx μ hg).trans (wh_eN_lt_lgG hx hx1)

/-- **`G` IS GOOD UP TO EVERY LEVEL.** -/
theorem woGood_G {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) : WoGood woG ℓ where
  lev := hℓ
  γ_lt := gv_Om1_pos
  F_P := ⟨gcG 0, wo_G_fix hℓ⟩
  G_le := le_rfl
  S_lt1 := by
    have hG1 := gcG_SC 1
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix : veblen ℓ (gcG 1) = gcG 1 := gn_veb_fix hG1 (hℓ.2.2.trans (gfE_lt_G0.trans (gcG_lt zero_lt_one)))
    have h2 := (isNormal_veblen ℓ).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt zero_lt_one))
    show hdNx ℓ (gcG 0) < gcG 1
    rw [hdNx_fixP (wo_G_fix hℓ)]; rwa [hfix] at h2
  F_mem := fun S _ _ ha _ => gmS_G0_mem S ha
  S_mem := fun μ hμ _ S _ _ ha hb => by
    show hdNx μ (gcG 0) ∈ _
    rw [hdNx_fixP (wo_G_fix hμ)]
    exact CSet.phi_mem ((woLv μ hμ).L_mem S _ _ ha (max_lt_iff.1 hb).2) (CSet.succ_mem (gmS_G0_mem S ha))
  S_memW := fun μ hμ hle S _ _ ha hb => by
    show hdNx (μ + Om1) (gcG 0) ∈ _
    rw [hdNx_fixP (wo_G_fix (wo_lev_succ hμ hℓ hle))]
    exact CSet.phi_mem ((woLv μ hμ).succ.L_mem S _ _ ha (max_lt_iff.1 hb).2) (CSet.succ_mem (gmS_G0_mem S ha))
  F_code := fun _ _ _ _ _ _ _ => GxCl.atom (Set.mem_singleton _)
  F_cl := fun _ hZ _ _ _ _ _ => hZ.1
  S_cl := fun _ hZ _ _ => hZ.1
  rd := fun μ hμ _ x hx hx1 hg => by
    have hgx : gtc μ < x := (max_lt_iff.1 hg).2
    have hlt := wo_rdc_lt_lgG hμ hx hx1 hgx
    have hfix := hjG_fix hx hx1 (wo_one_le_rdc hμ hx) hlt
    refine ⟨⟨lgG x, hfix⟩, hlt, ?_⟩
    show hdNx (rdc μ x) (lgG x) < veblen (eN (max ω x)) (lgG x + 1)
    rw [max_eq_right (omega0_lt_inE hx).le, hdNx_fixP hfix]
    exact hd_veb_left_lt (rdc_lt_eN hx μ hgx) _
  S_pi := fun μ hμ _ σ ρ hB hg => by
    have hgσ : gtc μ < σ := (max_lt_iff.1 hg).2
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    exact hjG_S_pi hB (rdc_pi hB hμ.2.2 hgσ) (wo_one_le_rdc hμ hB.2.1)
      (wo_rdc_lt_lgG hμ hB.2.1 hρ1 (hgσ.trans hB.2.2.1)) (wo_one_le_rdc hμ hB.1) (wo_rdc_lt_lgG hμ hB.1 hσ1 hgσ)
  Zo_fix := whZo_fix
  Zo_G1 := fun _ hx hx1 => whZo_G1 hx hx1
  Fr_pi := fun hB _ => Go.goGl.ba_pi _ _ hB

/-! ## The instance: a pseudo-base of a level -/

/-- **A pseudo-base as a raw datum.** -/
def woQR {Λ : HnLv} {ν : Ordinal.{0}} (Q : HnVQ Λ ν) : WoR := ⟨Q.F, Q.Fr, Q.γ, Q.Zo⟩

section QInst

variable {ℓ : Ordinal.{0}} (hℓ : WmLev ℓ) (Q : HnVQ (woLv ℓ hℓ) 0)

include hℓ in
theorem wo_Q_g : gtc ℓ ≤ Q.γ := Q.lg

theorem wo_Q_l {x : Ordinal.{0}} (hx : InE x) (hγ : Q.γ < x) : (woLv ℓ hℓ).l x + 0 = rdc ℓ x := by
  rw [add_zero]; exact woLv_l hℓ hx ((wo_Q_g hℓ Q).trans_lt hγ)

theorem wo_Q_N : hdNx ((woLv ℓ hℓ).L + 0) Q.F = hdNx ℓ Q.F := by rw [add_zero]; rfl

/-- **EVERY PSEUDO-BASE OF A LEVEL `ℓ` IS GOOD UP TO `ℓ`.** -/
theorem woGood_Q : WoGood (woQR Q) ℓ where
  lev := hℓ
  γ_lt := Q.γ_lt
  F_P := by have := Q.F_P; rwa [add_zero] at this
  G_le := Q.G_lt.le
  S_lt1 := by show hdNx ℓ Q.F < _; rw [← wo_Q_N hℓ Q]; exact Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun μ hμ hle S _ _ ha hb => by
    have hFP : LuP ℓ Q.F := by have := Q.F_P; rwa [add_zero] at this
    rcases hle.lt_or_eq with hlt | rfl
    · show hdNx μ Q.F ∈ _
      rw [hdNx_fixP (wo_fix_of_LuP hFP hlt)]
      exact CSet.phi_mem ((woLv μ hμ).L_mem S _ _ ha (max_lt_iff.1 hb).2)
        (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
    · show hdNx μ Q.F ∈ _
      rw [← wo_Q_N hℓ Q]; exact Q.S_mem S ha (max_lt_iff.1 hb).1
  S_memW := fun μ hμ hle S _ _ ha hb => by
    have hFP : LuP ℓ Q.F := by have := Q.F_P; rwa [add_zero] at this
    rcases hle.lt_or_eq with hlt | heq
    · show hdNx (μ + Om1) Q.F ∈ _
      rw [hdNx_fixP (wo_fix_of_LuP hFP hlt)]
      exact CSet.phi_mem ((woLv μ hμ).succ.L_mem S _ _ ha (max_lt_iff.1 hb).2)
        (CSet.succ_mem (Q.F_mem S ha (max_lt_iff.1 hb).1))
    · show hdNx (μ + Om1) Q.F ∈ _
      rw [heq, ← wo_Q_N hℓ Q]; exact Q.S_mem S ha (max_lt_iff.1 hb).1
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (by rw [wo_Q_N hℓ Q]; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (by rw [wo_Q_N hℓ Q]; exact hyZ)
  S_cl := fun Z hZ hZ1 hc => Q.S_cl Z hZ hZ1 (by rw [wo_Q_N hℓ Q]; exact hc)
  rd := fun μ hμ hle x hx hx1 hg => by
    have hγ : Q.γ < x := (max_lt_iff.1 hg).1
    have hgℓ : gtc ℓ < x := (wo_Q_g hℓ Q).trans_lt hγ
    have hmon : rdc μ x ≤ rdc ℓ x := rdc_le_mono hx hℓ.2.2 hle hgℓ (max_lt_iff.1 hg).2
    have h1 := Q.Fr_P hx hx1 hγ
    have h2 := Q.Fr_gt hx hx1 hγ
    have h3 := Q.S_Zo hx hx1 hγ
    rw [wo_Q_l hℓ Q hx hγ] at h1 h2 h3
    exact ⟨hd_LuP_mono hmon h1, hmon.trans_lt h2, (hdNx_mono hmon _).trans_lt h3⟩
  S_pi := fun μ hμ hle σ ρ hB hg => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγσ : Q.γ < σ := (max_lt_iff.1 hg).1
    have hγρ : Q.γ < ρ := hγσ.trans hB.2.2.1
    have hgμσ : gtc μ < σ := (max_lt_iff.1 hg).2
    have hgμρ : gtc μ < ρ := hgμσ.trans hB.2.2.1
    rcases hle.lt_or_eq with hlt | heq
    · have hfix : ∀ {y}, InE y → y < Om1 → Q.γ < y → gtc μ < y →
          veblen ((woLv μ hμ).l y + 0) (Q.Fr y) = Q.Fr y := by
        intro y hy hy1 hγy hgμy
        have hgy : gtc ℓ < y := (wo_Q_g hℓ Q).trans_lt hγy
        rw [add_zero, woLv_l hμ hy hgμy]
        have h1 := Q.Fr_P hy hy1 hγy
        rw [wo_Q_l hℓ Q hy hγy] at h1
        exact wo_fix_of_LuP h1 (rdc_mono hy hℓ.2.2 hlt hgy hgμy)
      have hgt : ∀ {y}, InE y → y < Om1 → Q.γ < y → gtc μ < y → (woLv μ hμ).l y + 0 < Q.Fr y := by
        intro y hy hy1 hγy hgμy
        have hgy : gtc ℓ < y := (wo_Q_g hℓ Q).trans_lt hγy
        have h2 := Q.Fr_gt hy hy1 hγy
        rw [wo_Q_l hℓ Q hy hγy] at h2
        rw [add_zero, woLv_l hμ hy hgμy]
        exact (rdc_mono hy hℓ.2.2 hlt hgy hgμy).trans h2
      obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγσ
      have hh := hnv_glA_pi (woLv μ hμ) hB hgμσ hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
      rw [f2, hnv_glA_fixP (woLv μ hμ) hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (hfix hB.2.1 hρ1 hγρ hgμρ)
        (hgt hB.2.1 hρ1 hγρ hgμρ) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
        hnv_glA_fixP (woLv μ hμ) hB.1 hσ1 hB.1.pos (hfix hB.1 hσ1 hγσ hgμσ) (hgt hB.1 hσ1 hγσ hgμσ)
        (Q.Fr_lt1 hB.1 hσ1 hγσ)] at hh
      rwa [add_zero, add_zero, woLv_l hμ hB.2.1 hgμρ, woLv_l hμ hB.1 hgμσ] at hh
    · subst heq
      have := Q.S_pi hB hγσ
      rwa [wo_Q_l hμ Q hB.2.1 hγρ, wo_Q_l hμ Q hB.1 hγσ] at this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi

end QInst

end Googology.Trans.PoR.InaccPsi.R2.Wo
