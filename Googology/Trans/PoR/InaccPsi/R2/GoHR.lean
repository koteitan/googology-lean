import Googology.Trans.PoR.InaccPsi.R2.GoHG

/-!
# THE GENERIC HEREDITARY STEP: the order of the readings

The port of `R2.GnHR` (base `B`, reading `D.b`, digits `D.R`):

* `GoD.hR_succ`, `GoD.bpow_eq`, `GoD.lead_le`, `GoD.hR_bound_of` (**`c < B^κ ⇒ c(x) < b(x)^{κ(x)}`** once the readings
  of the codes below a bound `N > c, κ` are increasing), `GoD.hR_mono` (**the reading is strictly increasing**),
  `GoD.hR_bound`, `GoD.hR_lt_succ`, `GoD.hR_lt_E` (**the readings lie below every `ε`-number above `b(x)`**),
  `GoD.hR_lt_eNb` (**below `ε_{b(x)+1}`**), `GoD.hR_lt1` (**below `Γ_{x+2}`**).

No new axiom.  New definition: `GoD.HMonoAt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GoD

variable (D : GoD)

theorem hR_succ : ∀ b, b + 1 < D.NB → ∀ x : Ordinal.{0}, D.hR (b + 1) x = D.hR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < D.NB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (D.B) with hbE | hbE
  · rw [D.hR_low hbE, D.hR_low (D.B_lim.add_one_lt hbE), D.R_succ]
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := D.parts hbE hbB
  obtain ⟨e, hr1⟩ := D.succ_cnf hbE
  have hr1B : b % D.B ^ log (D.B) b + 1 < D.NB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, D.hR_cnf hk hd0 hdE hr1 (e ▸ hb1), IH _ hrb hr1B x, D.hR_dec hbE hbB x, add_assoc]

/-- The readings of the codes below `j` are below the reading of `j`. -/
def HMonoAt (D : GoD) (x j : Ordinal.{0}) : Prop := ∀ b, b < j → D.hG j < x → D.hG b < x → D.hR b x < D.hR j x

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem bpow_eq (k : Ordinal.{0}) : D.b x ^ k = ω ^ (D.b x * k) := by
  rw [opow_mul, show ω ^ D.b x = D.b x from D.b_E x hx hx1]

theorem lead_le {c : Ordinal.{0}} (hcE : D.B ≤ c) (hcB : c < D.NB) (hg : D.hG c < x) :
    D.b x ^ D.hR (log (D.B) c) x ≤ D.hR c x := by
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := D.parts hcE hcB
  obtain ⟨-, g1, -⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hg
  rw [D.hR_dec hcE hcB]
  calc D.b x ^ D.hR (log (D.B) c) x = D.b x ^ D.hR (log (D.B) c) x * 1 := (mul_one _).symm
    _ ≤ D.b x ^ D.hR (log (D.B) c) x * D.R (c / D.B ^ log (D.B) c) x :=
        mul_le_mul_left' (one_le_iff_pos.2 (D.R_pos x hx hx1 _ hd0 hdE g1)) _
    _ ≤ _ := le_self_add

theorem b_le_pow {k : Ordinal.{0}} (hk : k ≠ 0) (hkB : k < D.NB) (hg : D.hG k < x) :
    D.b x ≤ D.b x ^ D.hR k x := by
  calc D.b x = D.b x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ D.b x ^ D.hR k x :=
        opow_le_opow_right (D.b_E x hx hx1).pos (one_le_iff_pos.2 (D.hR_pos hx hx1 hk hkB hg))

/-- **`c < B^κ ⇒ c(x) < b(x)^{κ(x)}`**, once the readings are increasing at the codes below a bound `N > c, κ`. -/
theorem hR_bound_of {N : Ordinal.{0}} (hN : ∀ j, j < N → D.HMonoAt x j) : ∀ c, c < N → c < D.NB → D.hG c < x →
    ∀ κ, κ ≠ 0 → κ < N → κ < D.NB → D.hG κ < x → c < D.B ^ κ → D.hR c x < D.b x ^ D.hR κ x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcN hcB hg κ hκ hκN hκB hgκ hcκ
  have hGE := D.b_E x hx hx1
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg
    rw [D.hR_low hcE]; exact (D.R_lt_b x hx hx1 _ hcE hg).trans_le (D.b_le_pow hx hx1 hκ hκB hgκ)
  obtain ⟨hj, hd0, hdE, hr, -, hjc, hrc⟩ := D.parts hcE hcB
  obtain ⟨g0, g1, g2⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hg
  have hjk : log (D.B) c < κ := (lt_opow_iff_log_lt D.one_lt_B (D.ne_of_le hcE)).1 hcκ
  have hrr := IH _ hrc (hrc.trans hcN) (hrc.trans hcB) g2 _ hj (hjc.trans hcN) (hjc.trans hcB) g0 hr
  have hjx : D.hR (log (D.B) c) x < D.hR κ x := hN κ hκN _ hjk hgκ g0
  rw [D.hR_dec hcE hcB]
  calc D.b x ^ D.hR (log (D.B) c) x * D.R (c / D.B ^ log (D.B) c) x + D.hR (c % D.B ^ log (D.B) c) x
      < D.b x ^ D.hR (log (D.B) c) x * D.R (c / D.B ^ log (D.B) c) x + D.b x ^ D.hR (log (D.B) c) x :=
        (add_lt_add_iff_left _).2 hrr
    _ = D.b x ^ D.hR (log (D.B) c) x * (D.R (c / D.B ^ log (D.B) c) x + 1) := by rw [mul_add_one]
    _ ≤ D.b x ^ D.hR (log (D.B) c) x * D.b x :=
        mul_le_mul_left' (Order.add_one_le_of_lt (D.R_lt_b x hx hx1 _ hdE g1)) _
    _ = D.b x ^ (D.hR (log (D.B) c) x + 1) := by rw [opow_add, opow_one]
    _ ≤ D.b x ^ D.hR κ x := opow_le_opow_right hGE.pos (Order.add_one_le_of_lt hjx)

/-- **The reading is strictly increasing.** -/
theorem hR_mono : ∀ c, c < D.NB → D.HMonoAt x c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB b hbc hgc hgb
  have hIH : ∀ j, j < c → D.HMonoAt x j := fun j hj => IH j hj (hj.trans hcB)
  have hGE := D.b_E x hx hx1
  rcases lt_or_ge c (D.B) with hcE | hcE
  · have hbE := hbc.trans hcE
    rw [D.hG_low hcE] at hgc
    rw [D.hG_low hbE] at hgb
    rw [D.hR_low hcE, D.hR_low hbE]
    exact D.mono x hx hx1 _ hcE _ hbc hgc hgb
  obtain ⟨hjc0, -, -, -, -, hjc, -⟩ := D.parts hcE hcB
  obtain ⟨gc0, gc1, gc2⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hgc
  rcases lt_or_ge b (D.B) with hbE | hbE
  · rw [D.hG_low hbE] at hgb
    rw [D.hR_low hbE]
    exact ((D.R_lt_b x hx hx1 _ hbE hgb).trans_le (D.b_le_pow hx hx1 hjc0 (hjc.trans hcB) gc0)).trans_le
      (D.lead_le hx hx1 hcE hcB hgc)
  have hbB : b < D.NB := hbc.trans hcB
  obtain ⟨-, -, -, -, -, hjb, -⟩ := D.parts hbE hbB
  obtain ⟨gb0, gb1, gb2⟩ := D.parts_g (omega0_lt_inE hx) hbE hbB hgb
  have hkk : log (D.B) b ≤ log (D.B) c := log_mono_right _ hbc.le
  rcases hkk.lt_or_eq with hlt | heq
  · have hb1 : b < D.B ^ (log (D.B) b + 1) :=
      (lt_opow_iff_log_lt D.one_lt_B (D.ne_of_le hbE)).2 (lt_add_one _)
    have hs1 : log (D.B) b + 1 ≤ log (D.B) c := Order.add_one_le_of_lt hlt
    have hs1c : log (D.B) b + 1 < c := lt_of_le_of_lt hs1 hjc
    have hs1B : log (D.B) b + 1 < D.NB := hs1c.trans hcB
    have hgs : D.hG (log (D.B) b + 1) < x := D.hG_succ (ev_isSuccLimit_of_inE hx) _ hs1B gb0
    have hmono : D.hR (log (D.B) b) x < D.hR (log (D.B) c) x := hIH _ hjc _ hlt gc0 gb0
    calc D.hR b x < D.b x ^ D.hR (log (D.B) b + 1) x :=
          D.hR_bound_of hx hx1 hIH b hbc hbB hgb _ (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1c hs1B hgs hb1
      _ = D.b x ^ (D.hR (log (D.B) b) x + 1) := by rw [D.hR_succ _ hs1B]
      _ ≤ D.b x ^ D.hR (log (D.B) c) x := opow_le_opow_right hGE.pos (Order.add_one_le_of_lt hmono)
      _ ≤ D.hR c x := D.lead_le hx hx1 hcE hcB hgc
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrc⟩ := D.parts hcE hcB
  obtain ⟨-, hd0', hdE', hr', hdec', -, hrb⟩ := D.parts hbE hbB
  rw [heq] at hd0' hdE' hr' hdec' gb1 gb2 hrb
  set k := log (D.B) c with hkdef
  set d := c / D.B ^ k
  set r := c % D.B ^ k
  set d' := b / D.B ^ k
  set r' := b % D.B ^ k
  have hdd : d' ≤ d := by
    by_contra hlt
    push Not at hlt
    have : c < b := by
      calc c = D.B ^ k * d + r := hdec.symm
        _ < D.B ^ k * d + D.B ^ k := (add_lt_add_iff_left _).2 hr
        _ = D.B ^ k * (d + 1) := by rw [mul_add_one]
        _ ≤ D.B ^ k * d' := mul_le_mul_left' (Order.add_one_le_of_lt hlt) _
        _ ≤ b := by rw [← hdec']; exact le_self_add
    exact absurd hbc (not_lt.2 this.le)
  have eb : D.hR b x = D.b x ^ D.hR k x * D.R d' x + D.hR r' x := by rw [D.hR_dec hbE hbB, heq]
  have ec : D.hR c x = D.b x ^ D.hR k x * D.R d x + D.hR r x := D.hR_dec hcE hcB x
  rw [eb, ec]
  rcases hdd.lt_or_eq with hd | hd
  · have hr'c : r' < c := hrb.trans hbc
    have hrb' := D.hR_bound_of hx hx1 hIH r' hr'c (hr'c.trans hcB) gb2 k hk hjc (hjc.trans hcB) gc0 hr'
    calc D.b x ^ D.hR k x * D.R d' x + D.hR r' x < D.b x ^ D.hR k x * D.R d' x + D.b x ^ D.hR k x :=
          (add_lt_add_iff_left _).2 hrb'
      _ = D.b x ^ D.hR k x * (D.R d' x + 1) := by rw [mul_add_one]
      _ ≤ D.b x ^ D.hR k x * D.R d x :=
          mul_le_mul_left' (Order.add_one_le_of_lt (D.mono x hx hx1 _ hdE _ hd gc1 gb1)) _
      _ ≤ _ := le_self_add
  · have hrr : r' < r := by
      have hb' : b = D.B ^ k * d + r' := by rw [← hd]; exact hdec'.symm
      have hc' : c = D.B ^ k * d + r := hdec.symm
      have h3 := hbc
      rw [hb', hc'] at h3
      exact (add_lt_add_iff_left _).1 h3
    rw [hd]
    exact (add_lt_add_iff_left _).2 (hIH r hrc r' hrr gc2 gb2)

/-- **`c < B^κ ⇒ c(x) < b(x)^{κ(x)}`.** -/
theorem hR_bound {c κ : Ordinal.{0}} (hcB : c < D.NB) (hg : D.hG c < x) (hκ : κ ≠ 0) (hκB : κ < D.NB)
    (hgκ : D.hG κ < x) (hcκ : c < D.B ^ κ) : D.hR c x < D.b x ^ D.hR κ x :=
  D.hR_bound_of hx hx1 (fun j hj => D.hR_mono hx hx1 j hj) c hcB hcB hg κ hκ hκB hκB hgκ hcκ

/-- `c(x) < b(x)^{(log_B c)(x)+1}`. -/
theorem hR_lt_succ {c : Ordinal.{0}} (hcE : D.B ≤ c) (hcB : c < D.NB) (hg : D.hG c < x) :
    D.hR c x < D.b x ^ (D.hR (log (D.B) c) x + 1) := by
  obtain ⟨-, -, -, -, -, hjc, -⟩ := D.parts hcE hcB
  obtain ⟨g0, -, -⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hg
  have hs1B : log (D.B) c + 1 < D.NB := lt_of_le_of_lt (Order.add_one_le_of_lt hjc) hcB
  have hgs : D.hG (log (D.B) c + 1) < x := D.hG_succ (ev_isSuccLimit_of_inE hx) _ hs1B g0
  have hb1 : c < D.B ^ (log (D.B) c + 1) :=
    (lt_opow_iff_log_lt D.one_lt_B (D.ne_of_le hcE)).2 (lt_add_one _)
  rw [← D.hR_succ _ hs1B]
  exact D.hR_bound hx hx1 hcB hg (lt_of_le_of_lt zero_le (lt_add_one _)).ne' hs1B hgs hb1

/-- **The readings lie below every `ε`-number `u > b(x)`** (`ε_{b(x)+1}`, `Γ_{x+2}`, …). -/
theorem hR_lt_E {u : Ordinal.{0}} (hu : InE u) (heu : D.b x < u) : ∀ c, c < D.NB → D.hG c < x → D.hR c x < u := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcB hg
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg; rw [D.hR_low hcE]; exact (D.R_lt_b x hx hx1 _ hcE hg).trans heu
  obtain ⟨-, -, -, -, -, hjc, -⟩ := D.parts hcE hcB
  obtain ⟨g0, -, -⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hg
  have hK := IH _ hjc (hjc.trans hcB) g0
  refine (D.hR_lt_succ hx hx1 hcE hcB hg).trans ?_
  rw [D.bpow_eq hx hx1]
  have h2 : D.b x * (D.hR (log (D.B) c) x + 1) < u :=
    hu.mul_lt heu ((inE_indec hu).add_lt hK (one_lt_omega0.trans (omega0_lt_inE hu)))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h2
  rwa [show ω ^ u = u from hu] at this

/-- **The readings lie below `ε_{b(x)+1}`.** -/
theorem hR_lt_eNb {c : Ordinal.{0}} (hc : c < D.NB) (hg : D.hG c < x) : D.hR c x < eN (D.b x) :=
  D.hR_lt_E hx hx1 (eN_E _) (lt_eN _) c hc hg

/-- **The readings lie below `Γ_{x+2}`.** -/
theorem hR_lt1 {c : Ordinal.{0}} (hc : c < D.NB) (hg : D.hG c < x) : D.hR c x < gq 1 x :=
  (D.hR_lt_eNb hx hx1 hc hg).trans (D.eN_b_lt1 hx hx1)

end Base


end GoD

end Googology.Trans.PoR.InaccPsi.R2.Go
