import Googology.Trans.PoR.InaccPsi.R2.XcCode

/-!
# XcSeq: SEQUENCES OF CODES FOR ANY CODE INTERFACE, AND THE THREE TRANSFERS

`Ws.BFs` / `Ws.BSq` / `Ws.ws_pre` / `Ws.ws_dig` / `Ws.ws_pow` are stated for the (A2) gate `Ws.gh`.  Here they are
stated once for EVERY code interface `C : Ws.WsC` (gate `C.g`, `Ω₁`-sequences `C.Seq1`):

* `XFs C M c`, `XSq C M c`, `XCls C M c` (`ω`- / `Ω₁`-sequences in the mode `M`, gates bounded by `C.g c`);
* `xc_pre`, `xc_dig`, `xc_pow` (**THE PREFIX, DIGIT AND POWER TRANSFERS** for every `C`);
* `xcls_of_A2` (**an (A2) sequence below `G` is an `xcA3` sequence**: below `G` the two interfaces agree).

No new axiom.  New definitions: `XFs`, `XSq`, `XCls`.
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
  Googology.Trans.PoR.InaccPsi.R2.Xc

namespace Googology.Trans.PoR.InaccPsi.R2.Xc

variable (C : WsC)

/-- **AN `ω`-SEQUENCE IN THE MODE `M`** for `c` with gates `C.g c_k ≤ C.g c`. -/
def XFs (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop :=
  ∃ cs : ℕ → Ordinal.{0}, (∀ k, M (cs k)) ∧ (∀ k, cs k < cs (k + 1)) ∧ (∀ k, cs k < c) ∧
    (∀ t, t < c → ∃ k, t < cs k) ∧ ∀ k, C.g (cs k) ≤ C.g c

/-- **AN `Ω₁`-SEQUENCE IN THE MODE `M`** for `c` (`C.Seq1`). -/
def XSq (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop :=
  ∃ s : Ordinal.{0} → Ordinal.{0}, C.Seq1 c s ∧ ∀ μ, μ < Om1 → M (s μ)

/-- **THE CLASSIFICATION OF `c` IN THE MODE `M`** for `C`. -/
def XCls (M : Ordinal.{0} → Prop) (c : Ordinal.{0}) : Prop := XFs C M c ∨ XSq C M c

variable {C}

theorem xcls_mono {M M' : Ordinal.{0} → Prop} (hMM : ∀ t, M t → M' t) {c : Ordinal.{0}} (h : XCls C M c) :
    XCls C M' c := by
  rcases h with ⟨cs, h1, h2, h3, h4, h5⟩ | ⟨s, hs, h1⟩
  · exact Or.inl ⟨cs, fun k => hMM _ (h1 k), h2, h3, h4, h5⟩
  · exact Or.inr ⟨s, hs, fun μ hμ => hMM _ (h1 μ hμ)⟩

/-- **THE PREFIX TRANSFER** for every code interface. -/
theorem xc_pre {M : Ordinal.{0} → Prop} {A T Pg : Ordinal.{0}} (hT : XCls C M T)
    (hg : ∀ t, t < T → C.g (A + t) = max Pg (C.g t)) (hgT : max Pg (C.g T) ≤ C.g (A + T))
    (hgx : ∀ x, InE x → C.g (A + T) < x → Pg < x ∧ C.g T < x) (hM : ∀ t, M t → M (A + t)) :
    XCls C M (A + T) := by
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
    · show C.g (A + s μ) < x
      rw [hg _ (s1 μ (hμ.trans hx1)).2]
      exact max_lt (hgx x hx hgx').1 (s3 x hx hx1 (hgx x hx hgx').2 μ hμ)
    · rcases lt_or_ge b A with hbA | hbA
      · exact ⟨0, hσ.pos, hbA.trans_le le_self_add⟩
      · obtain ⟨u, rfl⟩ := exists_add_of_le hbA
        have hu : u < T := (add_lt_add_iff_left A).1 hb
        have hgu : C.g u < σ := by
          have := hg u hu; change C.g (A + u) < σ at hgb; rw [this] at hgb; exact (le_max_right _ _).trans_lt hgb
        obtain ⟨μ, hμ, hlt⟩ := s4 σ hσ hσ1 u hu hgu
        exact ⟨μ, hμ, (add_lt_add_iff_left A).2 hlt⟩

/-- **THE DIGIT TRANSFER** for every code interface. -/
theorem xc_dig {M : Ordinal.{0} → Prop} {P D : Ordinal.{0}} (hP : P ≠ 0) (hD : XCls C (fun _ => True) D)
    (hFs : ∀ q, 0 < q → q < D → C.g q ≤ C.g D → C.g (P * q) ≤ C.g (P * D))
    (hgx : ∀ x, InE x → C.g (P * D) < x → C.g D < x ∧ ∀ q, 0 < q → q < D → C.g q < x → C.g (P * q) < x)
    (hcof : ∀ b σ, InE σ → P ≤ b → b < P * D → C.g b < σ → C.g (b / P) < σ)
    (hM : ∀ q, 0 < q → M (P * q)) : XCls C M (P * D) := by
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

/-- **THE POWER TRANSFER** for every code interface. -/
theorem xc_pow {M : Ordinal.{0} → Prop} {e J : Ordinal.{0}} (he : 1 < e) (hD : XCls C (fun _ => True) J)
    (hFs : ∀ j, 1 ≤ j → j < J → C.g j ≤ C.g J → C.g (e ^ j) ≤ C.g (e ^ J))
    (hgx : ∀ x, InE x → C.g (e ^ J) < x → C.g J < x ∧ ∀ j, 1 ≤ j → j < J → C.g j < x → C.g (e ^ j) < x)
    (hcof : ∀ b σ, InE σ → e ≤ b → b < e ^ J → C.g b < σ → C.g (log e b) < σ)
    (hM : ∀ j : Ordinal.{0}, 1 ≤ j → M (e ^ j)) : XCls C M (e ^ J) := by
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

/-! ## Below `G` the (A2) sequences are (A3) sequences -/

/-- **An (A2) `Ω₁`-sequence below `G` is an `xcA3` one.** -/
theorem xc_seq_of_A2 {a : Ordinal.{0}} {s : Ordinal.{0} → Ordinal.{0}} (ha : a < gcG 0) (h : wsA2.Seq1 a s) :
    xcA3.Seq1 a s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun x hx hx1 hg μ hμ => ?_, fun σ hσ hσ1 b hb hg => ?_⟩
  · show xg (s μ) < x
    rw [xg_low ((h1 μ (hμ.trans hx1)).2.trans ha)]
    exact h3 x hx hx1 (by show gh a < x; rw [← xg_low ha]; exact hg) μ hμ
  · exact h4 σ hσ hσ1 b hb (by show gh b < σ; rw [← xg_low (hb.trans ha)]; exact hg)

/-- **An (A2) classification below `G` is an `xcA3` classification.** -/
theorem xcls_of_A2 {M : Ordinal.{0} → Prop} {c : Ordinal.{0}} (hc : c < gcG 0) (h : BCls M c) : XCls xcA3 M c := by
  rcases h with ⟨cs, h1, h2, h3, h4, h5⟩ | ⟨s, hs, h1⟩
  · refine Or.inl ⟨cs, h1, h2, h3, h4, fun k => ?_⟩
    show xg (cs k) ≤ xg c
    rw [xg_low ((h3 k).trans hc), xg_low hc]; exact h5 k
  · exact Or.inr ⟨s, xc_seq_of_A2 hc hs, h1⟩

end Googology.Trans.PoR.InaccPsi.R2.Xc
