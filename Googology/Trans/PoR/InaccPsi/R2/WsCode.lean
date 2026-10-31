import Googology.Trans.PoR.InaccPsi.R2.WoTop

/-!
# WsCode: THE CODE INTERFACE OF THE FAMILY OVER RAW DATA

`R2.Wo` builds a family of systems over raw base data at every level below `ε_{Ω₁+1}`; of the codes it uses only a
reading, a gate, a bound and a few facts about them.  This module states those facts ONCE as a structure `WsC`:

* the bound `Bd < Γ(1)` (closed under `+`, above `Ω₁`; round 120: was `Bd ≤ G`), the reading `R c x`, the gate `g c < Ω₁` (`g Ω₁ = 1`,
  `R Ω₁ x = x`), the successor laws `R (a + Ω₁) x = R a x + x`, `g a ≤ g (a + Ω₁)` and their `ε`-cut, `g (t+1)` below
  every `ε`-number above `g t`;
* `x ≤ R ℓ x < Γ_{x+2}` (round 120: was `< Γ_{x+1}`), monotonicity, COFINALITY (`ν < R c x` ⇒ `ν ≤ R b x` for a smaller code `b` with gate
  below `x`), Lemma EXACT (`R_pi`);
* the digit gate (`g_cl`) and membership (`L_mem`) of a level, an outer low field `Zo`; the facts of `G` as a base
  (`Bd ≤ G`, `R ℓ x < Γ_{x+1}`, `Zo` above every reading) are the predicate `WsCG` (round 120).

From these: `WsC.Lev` (the levels), `WsC.lv` (**THE LEVEL DATUM OF EVERY LEVEL**, an `Hn.HnLv` with `L = ℓ` and gate
`g ℓ` by definition), `WsC.Fs` (`ω`-sequences of levels), `WsC.Seq1` / `WsC.Fs1` (`Ω₁`-sequences), and the level
arithmetic used by the steps.  The two instances are `Ws.wsA1` (`rdc`, `gtc`, `ε_{Ω₁+1}`) and `Ws.wsA2` (`glR`,
`glG`, `G`).

No new axiom.  New definitions: `WsC`, `WsCG`, `WsC.Lev`, `WsC.rd`, `WsC.lv`, `WsC.Fs`, `WsC.Seq1`, `WsC.Fs1`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ws

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

/-- **THE CODE INTERFACE**: a bound, a reading, a gate and an outer low field with the facts the family over raw
data uses. -/
structure WsC where
  Bd : Ordinal.{0}
  R : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  g : Ordinal.{0} → Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  Om1_lt : Om1 < Bd
  Bd_lt1 : Bd < gcG 1
  add_lt : ∀ a b, a < Bd → b < Bd → a + b < Bd
  g_lt : ∀ a, a < Bd → g a < Om1
  R_Om1 : ∀ x, R Om1 x = x
  g_Om1 : g Om1 = 1
  succ_R : ∀ a, a < Bd → Om1 ∣ a → ∀ x, R (a + Om1) x = R a x + x
  succ_g : ∀ a, a < Bd → Om1 ∣ a → g a ≤ g (a + Om1)
  succ_g_lt : ∀ {x a : Ordinal.{0}}, InE x → a < Bd → Om1 ∣ a → g a < x → g (a + Om1) < x
  g_succ1 : ∀ {x t : Ordinal.{0}}, InE x → t < Bd → g t < x → g (t + 1) < x
  le_R : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → Om1 ≤ ℓ → ℓ < Bd → g ℓ < x → x ≤ R ℓ x
  R_lt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → ℓ < Bd → g ℓ < x → R ℓ x < gq 1 x
  R_mono : ∀ {x b c : Ordinal.{0}}, InE x → x < Om1 → c < Bd → b < c → g c < x → g b < x → R b x < R c x
  R_cof : ∀ {x c : Ordinal.{0}}, InE x → x < Om1 → c < Bd → g c < x → ∀ ν, ν < R c x →
    ∃ b, b < c ∧ g b < x ∧ ν ≤ R b x
  R_pi : ∀ {σ ρ a : Ordinal.{0}}, Bases σ ρ → a < Bd → g a < σ → R a ρ ∈ TB ρ σ ∧ pi σ ρ (R a ρ) = R a σ
  g_cl : ∀ ℓ, Om1 ≤ ℓ → Om1 ∣ ℓ → ℓ < Bd → ∀ Z y : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} y → ℓ ≤ y →
    y < Om 1 * (Om1 * (ℓ / (Om1 * Om1))) + Om 1 * Om 1 → g ℓ < Z
  L_mem : ∀ ℓ, ℓ < Bd → ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → g ℓ < b → ℓ ∈ S.CSet a b
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x

/-- **THE FACTS OF `G` AS A BASE** for a code interface (the fields `Bd ≤ G`, `R ℓ x < Γ_{x+1}` and the outer low
field above `hdNx (R ℓ x) (Γ_{x+1})` of `WsC` before round 120): asked only where `G` itself is the raw datum
(`wsGood_G`, `wsSh_hgU`, `wsV`, `wsSysAll`). -/
structure WsCG (C : WsC) : Prop where
  Bd_le : C.Bd ≤ gcG 0
  R_lt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → ℓ < C.Bd → C.g ℓ < x → C.R ℓ x < lgG x
  Zo_gt : ∀ {x ℓ : Ordinal.{0}}, InE x → x < Om1 → Om1 ≤ ℓ → ℓ < C.Bd → C.g ℓ < x →
    hdNx (C.R ℓ x) (lgG x) < C.Zo x

namespace WsC

variable (C : WsC)

/-- **A LEVEL**: `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < Bd`. -/
def Lev (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < C.Bd

/-- The reading of the level datum: `R ℓ x` (at least `x`) above the gate, `x` at or below it. -/
noncomputable def rd (ℓ x : Ordinal.{0}) : Ordinal.{0} := if C.g ℓ < x then max x (C.R ℓ x) else x

theorem rd_eq {ℓ x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : Om1 ≤ ℓ) (hB : ℓ < C.Bd) (hg : C.g ℓ < x) :
    C.rd ℓ x = C.R ℓ x := by
  unfold rd; rw [if_pos hg, max_eq_right (C.le_R hx hx1 h1 hB hg)]

theorem Bd_lt_G1 : C.Bd < gcG 1 := C.Bd_lt1

theorem lt_G (hG : WsCG C) {a : Ordinal.{0}} (h : a < C.Bd) : a < gcG 0 := h.trans_le hG.Bd_le

/-- The reading `rd ℓ x` is below `Γ_{x+1}` for a level `ℓ`. -/
theorem rd_lt0 (hG : WsCG C) {ℓ : Ordinal.{0}} (h : C.Lev ℓ) : ∀ x, InE x → x < Om1 → C.rd ℓ x < lgG x :=
  fun x hx hx1 => by
  unfold rd; split_ifs with hg
  · exact max_lt (lgG_facts hx hx1).2.1 (hG.R_lt hx hx1 h.2.2 hg)
  · exact (lgG_facts hx hx1).2.1

/-- The reading `rd ℓ x` is below `Γ_{x+2}`. -/
theorem rd_lt1 {ℓ : Ordinal.{0}} (h : C.Lev ℓ) : ∀ x, InE x → x < Om1 → C.rd ℓ x < gq 1 x := fun x hx hx1 => by
  unfold rd; split_ifs with hg
  · exact max_lt (gm1_facts hx hx1).2.1 (C.R_lt hx hx1 h.2.2 hg)
  · exact (gm1_facts hx hx1).2.1

/-- **THE LEVEL DATUM OF EVERY LEVEL**: `L = ℓ`, gate `g ℓ`, reading `R ℓ x` above the gate. -/
noncomputable def lv (ℓ : Ordinal.{0}) (h : C.Lev ℓ) : HnLv where
  L := ℓ
  l := C.rd ℓ
  u := Om1 * (ℓ / (Om1 * Om1))
  q := (ℓ % (Om1 * Om1)) / Om1
  g := C.g ℓ
  g_lt := C.g_lt ℓ h.2.2
  q_lt := (wh_L_dec h.2.1).2
  OL := h.1
  L_G := h.2.2.trans C.Bd_lt1
  L_eq := by rw [← Br.Om1_eq]; exact (wh_L_dec h.2.1).1
  g_cl := C.g_cl ℓ h.1 h.2.1 h.2.2
  L_mem := C.L_mem ℓ h.2.2
  l_ge := fun x => by unfold rd; split_ifs; exacts [le_max_left _ _, le_rfl]
  l_lt := C.rd_lt1 h
  l_pi := fun σ ρ hB hg => by
    rw [C.rd_eq hB.2.1 hB.2.2.2 h.1 h.2.2 (hg.trans hB.2.2.1),
      C.rd_eq hB.1 (hB.2.2.1.trans hB.2.2.2) h.1 h.2.2 hg]
    exact C.R_pi hB h.2.2 hg

/-- **`C.lv ℓ` has the (A1)/(A2) bounds.** -/
theorem lv_G (hG : WsCG C) {ℓ : Ordinal.{0}} (h : C.Lev ℓ) : HnLvG (C.lv ℓ h) :=
  ⟨C.lt_G hG h.2.2, C.rd_lt0 hG h⟩

theorem lv_l {ℓ x : Ordinal.{0}} (h : C.Lev ℓ) (hx : InE x) (hx1 : x < Om1) (hg : C.g ℓ < x) :
    (C.lv ℓ h).l x = C.R ℓ x := C.rd_eq hx hx1 h.1 h.2.2 hg

/-- **AN `ω`-SEQUENCE OF LEVELS FOR `ℓ`** with gates `g ℓ_k ≤ g ℓ` (`Wm.WmFs`, `Wp.WpFs` for the instances). -/
def Fs (ℓ : Ordinal.{0}) : Prop :=
  ∃ ls : ℕ → Ordinal.{0}, (∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) ∧ (∀ k, ls k < ls (k + 1)) ∧ (∀ k, ls k < ℓ) ∧
    (∀ t, t < ℓ → ∃ k, t + 1 < ls k) ∧ ∀ k, C.g (ls k) ≤ C.g ℓ

/-- **AN `Ω₁`-SEQUENCE BELOW `a`** (`Wo.WoSeq1` with the gate `g`). -/
def Seq1 (a : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ μ, μ < Om1 → 1 ≤ s μ ∧ s μ < a) ∧ (∀ μ' μ, μ' < μ → μ < Om1 → s μ' < s μ) ∧
    (∀ x, InE x → x < Om1 → C.g a < x → ∀ μ, μ < x → C.g (s μ) < x) ∧
    ∀ σ, InE σ → σ < Om1 → ∀ b, b < a → C.g b < σ → ∃ μ, μ < σ ∧ b < s μ

/-- **AN `Ω₁`-SEQUENCE OF LEVELS BELOW `ℓ`.** -/
def Fs1 (ℓ : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  C.Seq1 ℓ s ∧ ∀ μ, μ < Om1 → Om1 ≤ s μ ∧ Om1 ∣ s μ

/-! ## Level arithmetic -/

variable {C}

/-- **A level is a limit**: `μ < ℓ` ⇒ `μ + 1 < ℓ`. -/
theorem lev_lim {ℓ μ : Ordinal.{0}} (hℓ : C.Lev ℓ) (h : μ < ℓ) : μ + 1 < ℓ := by
  obtain ⟨k, hk⟩ := hℓ.2.1
  rw [hk] at h ⊢
  have hq : μ / Om1 < k := (Ordinal.div_lt wh_Om1_pos.ne').2 h
  have hl : IsSuccLimit (Om1 * (μ / Om1) + Om1) := Ordinal.isSuccLimit_add _ gl_Om1_lim
  calc μ + 1 < Om1 * (μ / Om1) + Om1 := hl.add_one_lt (lt_mul_div_add μ wh_Om1_pos.ne')
  _ = Om1 * (μ / Om1 + 1) := by rw [mul_add_one]
  _ ≤ Om1 * k := mul_le_mul_left' (Order.add_one_le_of_lt hq) _

theorem lev_succ {μ ℓ : Ordinal.{0}} (hμ : C.Lev μ) (hℓ : C.Lev ℓ) (h : μ + Om1 ≤ ℓ) : C.Lev (μ + Om1) :=
  ⟨hμ.1.trans le_self_add, dvd_add hμ.2.1 (dvd_refl _), h.trans_lt hℓ.2.2⟩

theorem lev_Om1 : C.Lev Om1 := ⟨le_rfl, dvd_refl _, C.Om1_lt⟩

theorem Bd_lim : IsSuccLimit C.Bd := by
  refine Ordinal.isSuccLimit_iff.2 ⟨(wh_Om1_pos.trans C.Om1_lt).ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
  rw [← Ordinal.add_one_eq_succ]
  exact C.add_lt a 1 ha (wh_one_lt_Om1.trans C.Om1_lt)

theorem g_add_one_lt {x t : Ordinal.{0}} (hx : InE x) (ht : t < C.Bd) (hg : C.g t < x) : C.g (t + 1) < x :=
  C.g_succ1 hx ht hg

/-- **The gates of `μ` and `μ + Ω₁` have the same `ε`-cut.** -/
theorem g_succ_iff {μ x : Ordinal.{0}} (hμ : C.Lev μ) (hx : InE x) : C.g (μ + Om1) < x ↔ C.g μ < x :=
  ⟨fun h => (C.succ_g μ hμ.2.2 hμ.2.1).trans_lt h, fun h => C.succ_g_lt hx hμ.2.2 hμ.2.1 h⟩

theorem one_lt_inE {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) < x :=
  one_lt_omega0.trans (omega0_lt_inE hx)

/-- `max γ (g Ω₁) < x ↔ γ < x` at an `ε`-number `x`. -/
theorem cut1 {γ x : Ordinal.{0}} (hx : InE x) : max γ (C.g Om1) < x ↔ γ < x := by
  rw [max_lt_iff, C.g_Om1]; exact ⟨fun h => h.1, fun h => ⟨h, one_lt_inE hx⟩⟩

theorem R_le_mono {x b c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < C.Bd) (hbc : b ≤ c)
    (hgc : C.g c < x) (hgb : C.g b < x) : C.R b x ≤ C.R c x := by
  rcases hbc.lt_or_eq with h | rfl
  · exact (C.R_mono hx hx1 hc h hgc hgb).le
  · exact le_rfl

/-- **`R a x + 1 < R ℓ x`** for `a + 1 < ℓ` with gates below `x`. -/
theorem R_succ_lt {x a ℓ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hℓ : ℓ < C.Bd) (ha : a + 1 < ℓ)
    (hgℓ : C.g ℓ < x) (hga : C.g a < x) : C.R a x + 1 < C.R ℓ x := by
  have haB : a < C.Bd := (lt_add_one a).trans (ha.trans hℓ)
  have h1 := C.R_mono hx hx1 (ha.trans hℓ) (lt_add_one a) (C.g_succ1 hx haB hga) hga
  have h2 := C.R_mono hx hx1 hℓ ha hgℓ (C.g_succ1 hx haB hga)
  exact (Order.add_one_le_of_lt h1).trans_lt h2

/-- **`g ℓ < x` ⇒ `x ≤ R ℓ x`** and the reading is not `0`. -/
theorem R_ne0 {x ℓ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : Om1 ≤ ℓ) (hB : ℓ < C.Bd) (hg : C.g ℓ < x) :
    C.R ℓ x ≠ 0 := (hx.pos.trans_le (C.le_R hx hx1 h1 hB hg)).ne'

theorem one_le_R {x ℓ : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : Om1 ≤ ℓ) (hB : ℓ < C.Bd)
    (hg : C.g ℓ < x) : (1 : Ordinal.{0}) ≤ C.R ℓ x :=
  (one_lt_inE hx).le.trans (C.le_R hx hx1 h1 hB hg)

end WsC

end Googology.Trans.PoR.InaccPsi.R2.Ws
