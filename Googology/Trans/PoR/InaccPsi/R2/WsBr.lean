import Googology.Trans.PoR.InaccPsi.R2.WsA2

/-!
# WsBr: THE (A2) CLASSIFICATION BRACKET BY BRACKET — REDUCED TO THE `ε`-NUMBER CODES

A code `c ∈ [ε_{Ω₁+1}, G)` is `e^j·d + r` with `e = guE c` the largest `ε`-number `≤ c` (`Gl.gl_parts`).  Its
`ω`- or `Ω₁`-sequence (with the gate `gh = max 1 glG`) comes from that of a smaller part:

* the rest `r ≠ 0`: `A + r_k` / `A + s μ` (`ws_pre`, prefix `A = e^j·d`);
* the digit `d = d' + 1`, `d' ≠ 0`: `e^j·d' + t` over the sequence of `e^j` (`ws_pre`);
* the digit `d` a limit: `e^j·d_k` / `e^j·s μ` (`ws_dig`, `D = d`);
* the power `e^{j'+1}`, `j' ≥ 1`: `e^{j'}·e_k` over the sequence of `e` (`ws_dig`, `D = e`);
* the power `e^j`, `j` a limit: `e^{j_k}` / `e^{s μ}` (`ws_pow`);
* `e` itself: the BASE (an `ε`-number code, a Veblen node).

Below `ε_{Ω₁+1}` the sequences are those of `R2.Wo` / `R2.Wm`.  `ws_br` (**ONE WELL-FOUNDED INDUCTION**): if every
`ε`-number `e ∈ [ε_{Ω₁+1}, L)` has a sequence of levels (`BCls ML e`), then every limit code below `L` has a
sequence of codes, and every limit level below `L` that is not `Ω₁` or a successor level has a sequence of levels.
`wsCls_of_base`: the classification `WsCls wsA2 L` from the bases.

No new axiom.  New definitions: `ML`, `BFs`, `BSq`, `BCls`.
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
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp WsC

/-- A level (as a mode of sequences): `Ω₁ ≤ t`, `Ω₁ ∣ t`. -/
def ML (t : Ordinal.{0}) : Prop := Om1 ≤ t ∧ Om1 ∣ t

/-- **AN `ω`-SEQUENCE IN THE MODE `M`** for `c`, gates `gh c_k ≤ gh c`. -/
def BFs (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop :=
  ∃ cs : ℕ → Ordinal.{0}, (∀ k, M (cs k)) ∧ (∀ k, cs k < cs (k + 1)) ∧ (∀ k, cs k < c) ∧
    (∀ t, t < c → ∃ k, t < cs k) ∧ ∀ k, gh (cs k) ≤ gh c

/-- **AN `Ω₁`-SEQUENCE IN THE MODE `M`** for `c` (`wsA2.Seq1`). -/
def BSq (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop :=
  ∃ s : Ordinal.{0} → Ordinal.{0}, wsA2.Seq1 c s ∧ ∀ μ, μ < Om1 → M (s μ)

/-- **THE CLASSIFICATION OF `c` IN THE MODE `M`**. -/
def BCls (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop := BFs M c ∨ BSq M c

theorem bcls_mono {M M' : Ordinal.{0} → Prop} (hMM : ∀ t, M t → M' t) {c : Ordinal.{0}} (h : BCls M c) :
    BCls M' c := by
  rcases h with ⟨cs, h1, h2, h3, h4, h5⟩ | ⟨s, hs, h1⟩
  · exact Or.inl ⟨cs, fun k => hMM _ (h1 k), h2, h3, h4, h5⟩
  · exact Or.inr ⟨s, hs, fun μ hμ => hMM _ (h1 μ hμ)⟩

theorem one_le_gh (c : Ordinal.{0}) : (1 : Ordinal.{0}) ≤ gh c := le_max_left _ _

/-! ## The prefix transfer -/

/-- **THE PREFIX TRANSFER**: a sequence for `T` gives one for `A + T` (`A + t_k`, `A + s μ`) when the gate of
`A + t` (`t < T`) is `max Pg (gh t)`. -/
theorem ws_pre {M : Ordinal.{0} → Prop} {A T Pg : Ordinal.{0}} (hT : BCls M T)
    (hg : ∀ t, t < T → gh (A + t) = max Pg (gh t)) (hgT : max Pg (gh T) ≤ gh (A + T))
    (hgx : ∀ x, InE x → gh (A + T) < x → Pg < x ∧ gh T < x) (hM : ∀ t, M t → M (A + t)) :
    BCls M (A + T) := by
  rcases hT with ⟨cs, h1, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, sM⟩
  · refine Or.inl ⟨fun k => A + cs k, fun k => hM _ (h1 k), fun k => (add_lt_add_iff_left A).2 (h2 k),
      fun k => (add_lt_add_iff_left A).2 (h3 k), fun t ht => ?_, fun k => ?_⟩
    · rcases lt_or_ge t A with htA | htA
      · exact ⟨0, htA.trans_le le_self_add⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le htA
        obtain ⟨k, hk⟩ := h4 u ((add_lt_add_iff_left A).1 ht)
        exact ⟨k, (add_lt_add_iff_left A).2 hk⟩
    · rw [hg _ (h3 k)]; exact (max_le_max le_rfl (h5 k)).trans hgT
  · refine Or.inr ⟨fun μ => A + s μ, ⟨fun μ hμ => ⟨(s1 μ hμ).1.trans le_add_self,
      (add_lt_add_iff_left A).2 (s1 μ hμ).2⟩, fun μ' μ h hμ => (add_lt_add_iff_left A).2 (s2 μ' μ h hμ),
      fun x hx hx1 hgx' μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ hμ => hM _ (sM μ hμ)⟩
    · show gh (A + s μ) < x
      rw [hg _ (s1 μ (hμ.trans hx1)).2]
      exact max_lt (hgx x hx hgx').1 (s3 x hx hx1 (hgx x hx hgx').2 μ hμ)
    · rcases lt_or_ge b A with hbA | hbA
      · exact ⟨0, hσ.pos, hbA.trans_le le_self_add⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hbA
        have hu : u < T := (add_lt_add_iff_left A).1 hb
        have hgu : gh u < σ := by
          have := hg u hu; change gh (A + u) < σ at hgb; rw [this] at hgb; exact (le_max_right _ _).trans_lt hgb
        obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 u hu hgu
        exact ⟨μ, hμ, (add_lt_add_iff_left A).2 hlt⟩

/-! ## The digit transfer -/

/-- **THE DIGIT TRANSFER**: a sequence of codes for `D` gives one for `P·D` (`P·d_k`, `P·s μ`), `P ≠ 0`. -/
theorem ws_dig {M : Ordinal.{0} → Prop} {P D : Ordinal.{0}} (hP : P ≠ 0) (hD : BCls (fun _ => True) D)
    (hFs : ∀ q, 0 < q → q < D → gh q ≤ gh D → gh (P * q) ≤ gh (P * D))
    (hgx : ∀ x, InE x → gh (P * D) < x → gh D < x ∧ ∀ q, 0 < q → q < D → gh q < x → gh (P * q) < x)
    (hcof : ∀ b σ, InE σ → P ≤ b → b < P * D → gh b < σ → gh (b / P) < σ)
    (hM : ∀ q, 0 < q → M (P * q)) : BCls M (P * D) := by
  have hP0 : (0 : Ordinal.{0}) < P := pos_iff_ne_zero.2 hP
  rcases hD with ⟨cs, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · have hpos : ∀ k, 0 < cs (k + 1) := fun k => zero_le.trans_lt (h2 k)
    refine Or.inl ⟨fun k => P * cs (k + 1), fun k => hM _ (hpos k),
      fun k => mul_lt_mul_of_pos_left (h2 (k + 1)) hP0, fun k => mul_lt_mul_of_pos_left (h3 (k + 1)) hP0,
      fun t ht => ?_, fun k => hFs _ (hpos k) (h3 (k + 1)) (h5 (k + 1))⟩
    have hq : t / P < D := (Ordinal.div_lt hP).2 ht
    obtain ⟨k, hk⟩ := h4 _ hq
    refine ⟨k, (lt_mul_div_add t hP).trans_le ?_⟩
    rw [← mul_add_one]
    exact mul_le_mul_left' ((Order.add_one_le_of_lt hk).trans (h2 k).le) _
  · refine Or.inr ⟨fun μ => P * s μ, ⟨fun μ hμ => ⟨?_, mul_lt_mul_of_pos_left (s1 μ hμ).2 hP0⟩,
      fun μ' μ h hμ => mul_lt_mul_of_pos_left (s2 μ' μ h hμ) hP0, fun x hx hx1 hgx' μ hμ => ?_,
      fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ hμ => hM _ (zero_lt_one.trans_le (s1 μ hμ).1)⟩
    · exact (Order.one_le_iff_pos.2 hP0).trans (le_mul_of_one_le_right' (s1 μ hμ).1)
    · have h1 := hgx x hx hgx'
      exact h1.2 _ (zero_lt_one.trans_le (s1 μ (hμ.trans hx1)).1) (s1 μ (hμ.trans hx1)).2
        (s3 x hx hx1 h1.1 μ hμ)
    · rcases lt_or_ge b P with hbP | hbP
      · exact ⟨0, hσ.pos, hbP.trans_le (le_mul_of_one_le_right' (s1 0 gv_Om1_pos).1)⟩
      · have hq : b / P < D := (Ordinal.div_lt hP).2 hb
        obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 _ hq (hcof b σ hσ hbP hb hgb)
        refine ⟨μ, hμ, (lt_mul_div_add b hP).trans_le ?_⟩
        rw [← mul_add_one]
        exact mul_le_mul_left' (Order.add_one_le_of_lt hlt) _

/-! ## The power transfer -/

/-- **THE POWER TRANSFER**: a sequence of codes for `J` gives one for `e^J` (`e^{j_k}`, `e^{s μ}`), `1 < e`. -/
theorem ws_pow {M : Ordinal.{0} → Prop} {e J : Ordinal.{0}} (he : 1 < e) (hD : BCls (fun _ => True) J)
    (hFs : ∀ j, 1 ≤ j → j < J → gh j ≤ gh J → gh (e ^ j) ≤ gh (e ^ J))
    (hgx : ∀ x, InE x → gh (e ^ J) < x → gh J < x ∧ ∀ j, 1 ≤ j → j < J → gh j < x → gh (e ^ j) < x)
    (hcof : ∀ b σ, InE σ → e ≤ b → b < e ^ J → gh b < σ → gh (log e b) < σ)
    (hM : ∀ j : Ordinal.{0}, 1 ≤ j → M (e ^ j)) : BCls M (e ^ J) := by
  have he0 : (0 : Ordinal.{0}) < e := zero_lt_one.trans he
  have hle : ∀ j : Ordinal.{0}, 1 ≤ j → e ≤ e ^ j := fun j hj =>
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one e).symm
    _ ≤ e ^ j := opow_le_opow_right he0 hj
  rcases hD with ⟨cs, -, h2, h3, h4, h5⟩ | ⟨s, ⟨s1, s2, s3, s4⟩, -⟩
  · have hpos : ∀ k, 1 ≤ cs (k + 1) := fun k => Order.one_le_iff_pos.2 (zero_le.trans_lt (h2 k))
    refine Or.inl ⟨fun k => e ^ cs (k + 1), fun k => hM (cs (k + 1)) (hpos k),
      fun k => (opow_lt_opow_iff_right he).2 (h2 (k + 1)), fun k => (opow_lt_opow_iff_right he).2 (h3 (k + 1)),
      fun t ht => ?_, fun k => hFs _ (hpos k) (h3 (k + 1)) (h5 (k + 1))⟩
    rcases lt_or_ge t e with hte | hte
    · exact ⟨0, hte.trans_le (hle _ (hpos 0))⟩
    · have ht0 : t ≠ 0 := (he0.trans_le hte).ne'
      have hl : log e t < J := (lt_opow_iff_log_lt he ht0).1 ht
      obtain ⟨k, hk⟩ := h4 _ hl
      exact ⟨k, (lt_opow_succ_log_self he t).trans_le (opow_le_opow_right he0
        ((Order.add_one_le_of_lt hk).trans (h2 k).le))⟩
  · refine Or.inr ⟨fun μ => e ^ s μ, ⟨fun μ hμ => ⟨(Order.one_le_iff_pos.2 he0).trans (hle _ (s1 μ hμ).1),
      (opow_lt_opow_iff_right he).2 (s1 μ hμ).2⟩, fun μ' μ h hμ => (opow_lt_opow_iff_right he).2 (s2 μ' μ h hμ),
      fun x hx hx1 hgx' μ hμ => ?_, fun σ hσ hσ1 b hb hgb => ?_⟩, fun μ hμ => hM (s μ) (s1 μ hμ).1⟩
    · have h1 := hgx x hx hgx'
      exact h1.2 _ (s1 μ (hμ.trans hx1)).1 (s1 μ (hμ.trans hx1)).2 (s3 x hx hx1 h1.1 μ hμ)
    · rcases lt_or_ge b e with hbe | hbe
      · exact ⟨0, hσ.pos, hbe.trans_le (hle _ (s1 0 gv_Om1_pos).1)⟩
      · have hb0 : b ≠ 0 := (he0.trans_le hbe).ne'
        have hl : log e b < J := (lt_opow_iff_log_lt he hb0).1 hb
        obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 _ hl (hcof b σ hσ hbe hb hgb)
        exact ⟨μ, hμ, (lt_opow_succ_log_self he b).trans_le (opow_le_opow_right he0 (Order.add_one_le_of_lt hlt))⟩

end Googology.Trans.PoR.InaccPsi.R2.Ws
