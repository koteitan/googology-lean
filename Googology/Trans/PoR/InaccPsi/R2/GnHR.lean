import Googology.Trans.PoR.InaccPsi.R2.GnHG

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}`: the order of the readings

The port of `R2.GjHR` (base `Γ_{Ω₁+1}`, reading `Γ_{x+1}`, digits `Gl.glR`):

* `gnR_succ`, `gn_Gpow`, `gn_lead_le`, `gnR_bound_of` (**`c < G^κ ⇒ c(x) < Γ_{x+1}^{κ(x)}`** once the readings of the
  codes below a bound `N > c, κ` are increasing), `gnR_mono` (**the reading is strictly increasing**, by induction on
  the code, the exponents being smaller codes), `gnR_bound`, `gnR_lt_succ`, `gnR_lt_E` (**the readings lie below every
  `ε`-number above `Γ_{x+1}`**), `gnR_lt_eNG` (**below `ε_{Γ_{x+1}+1}`**), `gnR_lt1` (**below `Γ_{x+2}`**).

No new axiom.  New definition: `GnMonoAt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gnR_succ : ∀ b, b + 1 < gnB → ∀ x : Ordinal.{0}, gnR (b + 1) x = gnR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < gnB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (gcG 0) with hbE | hbE
  · rw [gnR_low hbE, gnR_low (gl_G0_lim.add_one_lt hbE), glR_succ_all]
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := gn_parts hbE hbB
  obtain ⟨e, hr1⟩ := gn_succ_cnf hbE
  have hr1B : b % gcG 0 ^ log (gcG 0) b + 1 < gnB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, gnR_cnf hk hd0 hdE hr1 (e ▸ hb1), IH _ hrb hr1B x, gnR_dec hbE hbB x, add_assoc]

/-- The readings of the codes below `j` are below the reading of `j`. -/
def GnMonoAt (x j : Ordinal.{0}) : Prop := ∀ b, b < j → gnG j < x → gnG b < x → gnR b x < gnR j x

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gn_Gpow (k : Ordinal.{0}) : lgG x ^ k = ω ^ (lgG x * k) := by
  rw [opow_mul, show ω ^ lgG x = lgG x from (lgG_facts hx hx1).2.2.2.1]

theorem gn_lead_le {c : Ordinal.{0}} (hcE : gcG 0 ≤ c) (hcB : c < gnB) (hg : gnG c < x) :
    lgG x ^ gnR (log (gcG 0) c) x ≤ gnR c x := by
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := gn_parts hcE hcB
  obtain ⟨-, g1, -⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hg
  rw [gnR_dec hcE hcB]
  calc lgG x ^ gnR (log (gcG 0) c) x = lgG x ^ gnR (log (gcG 0) c) x * 1 := (mul_one _).symm
    _ ≤ lgG x ^ gnR (log (gcG 0) c) x * glR (c / gcG 0 ^ log (gcG 0) c) x :=
        mul_le_mul_left' (one_le_iff_pos.2 (glR_pos hx hx1 hd0 hdE g1)) _
    _ ≤ _ := le_self_add

theorem gn_G_le_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < gnB) (hg : gnG k < x) :
    lgG x ≤ lgG x ^ gnR k x := by
  calc lgG x = lgG x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ lgG x ^ gnR k x :=
        opow_le_opow_right (lgG_facts hx hx1).2.2.2.1.pos (one_le_iff_pos.2 (gnR_pos hx hx1 hk hkB hg))

/-- **`c < G^κ ⇒ c(x) < Γ_{x+1}^{κ(x)}`**, once the readings are increasing at the codes below a bound `N > c, κ`. -/
theorem gnR_bound_of {N : Ordinal.{0}} (hN : ∀ j, j < N → GnMonoAt x j) : ∀ c, c < N → c < gnB → gnG c < x →
    ∀ κ, κ ≠ 0 → κ < N → κ < gnB → gnG κ < x → c < gcG 0 ^ κ → gnR c x < lgG x ^ gnR κ x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg κ hκ hκN hκB hgκ hcκ
  have hGE := (lgG_facts hx hx1).2.2.2.1
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg
    rw [gnR_low hcE]; exact (glR_lt_G hx hx1 hcE hg).trans_le (gn_G_le_pow hx hx1 hκ hκB hgκ)
  obtain ⟨hj, hd0, hdE, hr, -, hjc, hrc⟩ := gn_parts hcE hcB
  obtain ⟨g0, g1, g2⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hg
  have hjk : log (gcG 0) c < κ := (lt_opow_iff_log_lt gn_one_lt (gn_ne_of_le hcE)).1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 _ hj (hjc.trans hcN) (hjc.trans hcB) g0 hr
  have hjx : gnR (log (gcG 0) c) x < gnR κ x := hN κ hκN _ hjk hgκ g0
  rw [gnR_dec hcE hcB]
  calc lgG x ^ gnR (log (gcG 0) c) x * glR (c / gcG 0 ^ log (gcG 0) c) x + gnR (c % gcG 0 ^ log (gcG 0) c) x
      < lgG x ^ gnR (log (gcG 0) c) x * glR (c / gcG 0 ^ log (gcG 0) c) x + lgG x ^ gnR (log (gcG 0) c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = lgG x ^ gnR (log (gcG 0) c) x * (glR (c / gcG 0 ^ log (gcG 0) c) x + 1) := by rw [mul_add_one]
    _ ≤ lgG x ^ gnR (log (gcG 0) c) x * lgG x :=
        mul_le_mul_left' (Order.add_one_le_of_lt (glR_lt_G hx hx1 hdE g1)) _
    _ = lgG x ^ (gnR (log (gcG 0) c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ lgG x ^ gnR κ x := opow_le_opow_right hGE.pos (Order.add_one_le_of_lt hjx)

/-- **The reading is strictly increasing.** -/
theorem gnR_mono : ∀ c, c < gnB → GnMonoAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB b hbc hgc hgb
  have hIH : ∀ j, j < c → GnMonoAt x j := fun j hj => IH j hj (hj.trans hcB)
  have hGE := (lgG_facts hx hx1).2.2.2.1
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · have hbE := hbc.trans hcE
    rw [gnG_low hcE] at hgc
    rw [gnG_low hbE] at hgb
    rw [gnR_low hcE, gnR_low hbE]
    exact glR_mono hx hx1 hcE hbc hgc hgb
  obtain ⟨hjc0, -, -, -, -, hjc, -⟩ := gn_parts hcE hcB
  obtain ⟨gc0, gc1, gc2⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hgc
  rcases lt_or_ge b (gcG 0) with hbE | hbE
  · rw [gnG_low hbE] at hgb
    rw [gnR_low hbE]
    exact ((glR_lt_G hx hx1 hbE hgb).trans_le (gn_G_le_pow hx hx1 hjc0 (hjc.trans hcB) gc0)).trans_le
      (gn_lead_le hx hx1 hcE hcB hgc)
  have hbB : b < gnB := hbc.trans hcB
  obtain ⟨-, -, -, -, -, hjb, -⟩ := gn_parts hbE hbB
  obtain ⟨gb0, gb1, gb2⟩ := gn_parts_g (omega0_lt_inE hx) hbE hbB hgb
  have hkk : log (gcG 0) b ≤ log (gcG 0) c := log_mono_right _ hbc.le
  rcases hkk.lt_or_eq with hlt | heq
  · have hb1 : b < gcG 0 ^ (log (gcG 0) b + 1) :=
      (lt_opow_iff_log_lt gn_one_lt (gn_ne_of_le hbE)).2 (lt_add_one _)
    have hs1 : log (gcG 0) b + 1 ≤ log (gcG 0) c := Order.add_one_le_of_lt hlt
    have hs1c : log (gcG 0) b + 1 < c := lt_of_le_of_lt hs1 hjc
    have hs1B : log (gcG 0) b + 1 < gnB := hs1c.trans hcB
    have hgs : gnG (log (gcG 0) b + 1) < x := gnG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gb0
    have hmono : gnR (log (gcG 0) b) x < gnR (log (gcG 0) c) x := hIH _ hjc _ hlt gc0 gb0
    calc gnR b x < lgG x ^ gnR (log (gcG 0) b + 1) x :=
          gnR_bound_of hx hx1 hIH b hbc hbB hgb _ (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
      _ = lgG x ^ (gnR (log (gcG 0) b) x + 1) := by rw [gnR_succ _ hs1B]
      _ ≤ lgG x ^ gnR (log (gcG 0) c) x := opow_le_opow_right hGE.pos (Order.add_one_le_of_lt hmono)
      _ ≤ gnR c x := gn_lead_le hx hx1 hcE hcB hgc
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrc⟩ := gn_parts hcE hcB
  obtain ⟨-, hd0', hdE', hr', hdec', -, hrb⟩ := gn_parts hbE hbB
  rw [heq] at hd0' hdE' hr' hdec' gb1 gb2 hrb
  set k := log (gcG 0) c with hkdef
  set d := c / gcG 0 ^ k
  set r := c % gcG 0 ^ k
  set d' := b / gcG 0 ^ k
  set r' := b % gcG 0 ^ k
  have hdd : d' ≤ d := by
    by_contra hlt
    push Not at hlt
    have : c < b := by
      calc c = gcG 0 ^ k * d + r := hdec.symm
        _ < gcG 0 ^ k * d + gcG 0 ^ k := (add_lt_add_iff_left _).2 hr
        _ = gcG 0 ^ k * (d + 1) := by rw [mul_add_one]
        _ ≤ gcG 0 ^ k * d' := mul_le_mul_left' (Order.add_one_le_of_lt hlt) _
        _ ≤ b := by rw [← hdec']; exact le_self_add
    exact absurd hbc (not_lt.2 this.le)
  have eb : gnR b x = lgG x ^ gnR k x * glR d' x + gnR r' x := by rw [gnR_dec hbE hbB, heq]
  have ec : gnR c x = lgG x ^ gnR k x * glR d x + gnR r x := gnR_dec hcE hcB x
  rw [eb, ec]
  rcases hdd.lt_or_eq with hd | hd
  · have hr'c : r' < c := hrb.trans hbc
    have hrb' := gnR_bound_of hx hx1 hIH r' hr'c (hr'c.trans hcB) gb2 k hk hjc (hjc.trans hcB) gc0 hr'
    calc lgG x ^ gnR k x * glR d' x + gnR r' x < lgG x ^ gnR k x * glR d' x + lgG x ^ gnR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = lgG x ^ gnR k x * (glR d' x + 1) := by rw [mul_add_one]
      _ ≤ lgG x ^ gnR k x * glR d x :=
          mul_le_mul_left' (Order.add_one_le_of_lt (glR_mono hx hx1 hdE hd gc1 gb1)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = gcG 0 ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = gcG 0 ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hIH r hrc r' hrr gc2 gb2)

/-- **`c < G^κ ⇒ c(x) < Γ_{x+1}^{κ(x)}`.** -/
theorem gnR_bound {c κ : Ordinal.{0}} (hcB : c < gnB) (hg : gnG c < x) (hκ : κ ≠ 0) (hκB : κ < gnB)
    (hgκ : gnG κ < x) (hcκ : c < gcG 0 ^ κ) : gnR c x < lgG x ^ gnR κ x :=
  gnR_bound_of hx hx1 (fun j hj => gnR_mono hx hx1 j hj) c hcB hcB hg κ hκ hκB hκB hgκ hcκ

/-- `c(x) < Γ_{x+1}^{(log_G c)(x)+1}`. -/
theorem gnR_lt_succ {c : Ordinal.{0}} (hcE : gcG 0 ≤ c) (hcB : c < gnB) (hg : gnG c < x) :
    gnR c x < lgG x ^ (gnR (log (gcG 0) c) x + 1) := by
  obtain ⟨-, -, -, -, -, hjc, -⟩ := gn_parts hcE hcB
  obtain ⟨g0, -, -⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hg
  have hs1B : log (gcG 0) c + 1 < gnB := lt_of_le_of_lt (Order.add_one_le_of_lt hjc) hcB
  have hgs : gnG (log (gcG 0) c + 1) < x := gnG_succ (ev_isSuccLimit_of_inE hx) _ hs1B g0
  have hb1 : c < gcG 0 ^ (log (gcG 0) c + 1) :=
    (lt_opow_iff_log_lt gn_one_lt (gn_ne_of_le hcE)).2 (lt_add_one _)
  rw [← gnR_succ _ hs1B]
  exact gnR_bound hx hx1 hcB hg (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1B hgs hb1

/-- **The readings lie below every `ε`-number `u > Γ_{x+1}`** (`ε_{Γ_{x+1}+1}`, `Γ_{x+2}`, …). -/
theorem gnR_lt_E {u : Ordinal.{0}} (hu : InE u) (heu : lgG x < u) : ∀ c, c < gnB → gnG c < x → gnR c x < u := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB hg
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg; rw [gnR_low hcE]; exact (glR_lt_G hx hx1 hcE hg).trans heu
  obtain ⟨-, -, -, -, -, hjc, -⟩ := gn_parts hcE hcB
  obtain ⟨g0, -, -⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hg
  have hK := IH _ hjc (hjc.trans hcB) g0
  refine (gnR_lt_succ hx hx1 hcE hcB hg).trans ?_
  rw [gn_Gpow hx hx1]
  have h2 : lgG x * (gnR (log (gcG 0) c) x + 1) < u :=
    hu.mul_lt heu ((inE_indec hu).add_lt hK (one_lt_omega0.trans (omega0_lt_inE hu)))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
  rwa [show ω ^ u = u from hu] at this

/-- **The readings lie below `ε_{Γ_{x+1}+1}`.** -/
theorem gnR_lt_eNG {c : Ordinal.{0}} (hc : c < gnB) (hg : gnG c < x) : gnR c x < eN (lgG x) :=
  gnR_lt_E hx hx1 (eN_E _) (lt_eN _) c hc hg

/-- **The readings lie below `Γ_{x+2}`.** -/
theorem gnR_lt1 {c : Ordinal.{0}} (hc : c < gnB) (hg : gnG c < x) : gnR c x < gq 1 x :=
  (gnR_lt_eNG hx hx1 hc hg).trans (gn_eNG_lt1 hx hx1)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Gn
