import Googology.Trans.PoR.InaccPsi.R2.WsBrI

/-!
# WsEps: THE `ε`-NUMBER BASES UP TO `ε_{Ω₁+ω}`; THE REFUTE-FIRST FINDING AT `ε_{Ω₁+1}`

* `ws_glG_E_noFs` (**REFUTE FIRST**: `ε_{Ω₁+1}` is an (A2) level of the remaining case of `Wp.WpOm1Step` — not `Ω₁`,
  not a successor — with NO `Wp.WpFs` sequence (every level below has gate `glG ≥ 1 > 0 = glG ε_{Ω₁+1}`) and NO
  `Ω₁`-sequence (its cofinality is `ω`): a classification with the gate `glG` is false there; with `gh = max 1 glG`
  the towers `Ω₁, Ω₁^{Ω₁}, …` are an `ω`-sequence, `ws_base_E`);
* `ws_tw_*` (towers `e, e^e, …` over an `ε`-number code: increasing, cofinal in `ε_{e+1}`, gate `≤ glQE e`),
  `ws_base_succ` (**THE BASE `ε_{e+1}` FROM THE TOWER OVER `e`**);
* `wsEp n = ε_{Ω₁+1+n} = φ(1, Ω₁+n+1)`, `ws_base_ep` (every `n`), `ws_base_top` (**`ε_{Ω₁+ω}` FROM `wsEp n`**);
* `ws_base_w` (**`WsBase (ε_{Ω₁+ω} + 1)`, UNCONDITIONAL**), `wsCls_w` (**THE (A2) CLASSIFICATION UP TO
  `ε_{Ω₁+ω}`**, UNCONDITIONAL).

No new axiom.  New definitions: `wsEp`, `wsLw`.
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

/-! ## Refute first: the gate `glG` at `ε_{Ω₁+1}` -/

/-- **Every level below `ε_{Ω₁+1}` has gate `≥ 1`.** -/
theorem ws_gtc_pos {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) : (1 : Ordinal.{0}) ≤ gtc a :=
  (Order.one_le_iff_pos.2 (div_opow_log_pos Om1 ha)).trans (gtc_parts ha haW).2.1

theorem ws_woT_E : ∀ t, t < gfE → ∃ k : ℕ, t < woT k := fun _ ht => woU_cof gl_Om1_E ht

/-- **REFUTE FIRST**: `ε_{Ω₁+1}` is an (A2) level that is not `Ω₁`, not a successor level, has no `Wp.WpFs`
sequence and no `Ω₁`-sequence. -/
theorem ws_glG_E_noFs : WpLev gfE ∧ gfE ≠ Om1 ∧ (¬ ∃ ℓ', WpLev ℓ' ∧ gfE = ℓ' + Om1) ∧ ¬ WpFs gfE ∧
    ¬ ∃ s, wsA2.Seq1 gfE s := by
  have hE := eW_E
  refine ⟨⟨Om1_lt_eW.le, wp_Om1_dvd_E hE Om1_lt_eW, gfE_lt_G0⟩, Om1_lt_eW.ne', fun ⟨ℓ', _, he⟩ => ?_,
    fun ⟨ls, h1, _, h3, _, h5⟩ => ?_, fun ⟨s, s1, s2, _, s4⟩ => ?_⟩
  · have hlt : ℓ' < gfE := by rw [he]; exact lt_add_of_pos_right _ wh_Om1_pos
    exact absurd he (eW_indec.add_lt hlt Om1_lt_eW).ne'
  · have h := h5 0
    rw [glG_low (h3 0), glG_E] at h
    have h1' := ws_gtc_pos ((wh_Om1_pos.trans_le (h1 0).1).ne') (h3 0)
    exact absurd (h1'.trans h) (not_le.2 zero_lt_one)
  · -- `σ = ε₀`: every tower `woT (k+1)` lies below some `s μ`, `μ < ε₀`, so `s ε₀ ≥ ε_{Ω₁+1}`
    set σ : Ordinal.{0} := eN 0 with hσ_def
    have hσE : InE σ := eN_E 0
    have hσ1 : σ < Om1 := eN_lt_Om1K gv_Om1_pos
    have hk : ∀ k : ℕ, ∃ μ, μ < σ ∧ woT (k + 1) < s μ := fun k => by
      refine s4 σ hσE hσ1 _ (woT_facts (k + 1)).1 ?_
      show gh (woT (k + 1)) < σ
      rw [gh_lt_iff hσE, glG_low (woT_facts (k + 1)).1, (woT_facts (k + 1)).2.1]
      exact one_lt_omega0.trans (omega0_lt_inE hσE)
    obtain ⟨k, hkσ⟩ := ws_woT_E (s σ) (s1 σ hσ1).2
    obtain ⟨μ, hμ, hlt⟩ := hk k
    exact absurd ((hkσ.trans (woT_lt_succ k)).trans (hlt.trans (s2 μ σ hμ hσ1))) (lt_irrefl _)

/-- **THE BASE `ε_{Ω₁+1}`**: the towers `woT (k+1)` with the gate `gh = 1`. -/
theorem ws_base_E : BCls ML gfE := by
  refine Or.inl ⟨fun k => woT (k + 1), fun k => ⟨(woT_lev k).1, (woT_lev k).2.1⟩, fun k => woT_lt_succ (k + 1),
    fun k => (woT_facts (k + 1)).1, fun t ht => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := ws_woT_E t ht
    exact ⟨k, hk.trans (woT_lt_succ k)⟩
  · show max 1 (glG (woT (k + 1))) ≤ max 1 (glG gfE)
    rw [glG_low (woT_facts (k + 1)).1, (woT_facts (k + 1)).2.1, glG_E, max_self, max_eq_left zero_le]

/-! ## The tower over an `ε`-number code -/

section Tw

variable {e : Ordinal.{0}} (he : InE e)
include he

theorem ws_tw_one : woU e 1 = e := by show e ^ (1 : Ordinal.{0}) = e; exact opow_one e

theorem ws_tw_le : ∀ k : ℕ, woU e k ≤ woU e (k + 1)
  | 0 => by rw [ws_tw_one he]; exact (Lu.lu_one_lt_E he).le
  | k + 1 => opow_le_opow_right he.pos (ws_tw_le k)

theorem ws_tw_lt : ∀ k : ℕ, woU e (k + 1) < woU e (k + 2)
  | 0 => by
    show woU e 1 < e ^ woU e 1
    rw [ws_tw_one he]
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one e).symm
    _ < e ^ e := (opow_lt_opow_iff_right (Lu.lu_one_lt_E he)).2 (Lu.lu_one_lt_E he)
  | k + 1 => (opow_lt_opow_iff_right (Lu.lu_one_lt_E he)).2 (ws_tw_lt k)

theorem ws_tw_ge : ∀ k : ℕ, e ≤ woU e (k + 1)
  | 0 => (ws_tw_one he).ge
  | k + 1 => (ws_tw_ge k).trans (ws_tw_lt he k).le

variable (hOe : Om1 < e) (hNG : eN e < gcG 0)
include hOe hNG

theorem ws_tw_gate : ∀ k : ℕ, glG (woU e (k + 1)) ≤ glQE e
  | 0 => by rw [ws_tw_one he, glG_base he hOe ((lt_eN e).trans hNG)]
  | k + 1 => by
    have ht0 : woU e (k + 1) ≠ 0 := (he.pos.trans_le (ws_tw_ge he k)).ne'
    have hN : e ^ woU e (k + 1) * 1 + 0 < eN e := by rw [mul_one, add_zero]; exact woU_lt_eN he (k + 2)
    have h := glG_cnf he hOe ht0 one_ne_zero (Lu.lu_one_lt_E he) (opow_pos _ he.pos) hN (hN.trans hNG)
    rw [mul_one, add_zero] at h
    show glG (e ^ woU e (k + 1)) ≤ _
    rw [h, glQ_one, glG_zero, max_self, max_eq_left zero_le]
    exact max_le le_rfl ((glQ_le _).trans (ws_tw_gate k))

/-- **THE BASE `ε_{e+1}` FROM THE TOWER OVER `e`**, when `max 1 (glQE e) ≤ gh ε_{e+1}`. -/
theorem ws_base_succ (hg : max 1 (glQE e) ≤ gh (eN e)) : BCls ML (eN e) := by
  refine Or.inl ⟨fun k => woU e (k + 2), fun k => ?_, fun k => ws_tw_lt he (k + 1),
    fun k => woU_lt_eN he (k + 2), fun t ht => ?_, fun k => ?_⟩
  · have := ws_ML_mul (q := 1) he hOe (he.pos.trans_le (ws_tw_ge he k)).ne' zero_lt_one
    rwa [mul_one] at this
  · obtain ⟨k, hk⟩ := woU_cof he ht
    exact ⟨k, hk.trans_le ((ws_tw_le he k).trans (ws_tw_le he (k + 1)))⟩
  · exact (max_le_max le_rfl (ws_tw_gate he hOe hNG (k + 1))).trans hg

end Tw

/-! ## The `ε`-numbers `ε_{Ω₁+1+n}` and `ε_{Ω₁+ω}` -/

/-- `ε_{Ω₁+1+n} = φ(1, Ω₁ + n + 1)`. -/
noncomputable def wsEp (n : ℕ) : Ordinal.{0} := veblen 1 (Om1 + (n : Ordinal.{0}) + 1)

/-- `ε_{Ω₁+ω} = φ(1, Ω₁ + ω)`. -/
noncomputable def wsLw : Ordinal.{0} := veblen 1 (Om1 + ω)

theorem wsEp_zero : wsEp 0 = gfE := by rw [wsEp, Nat.cast_zero, add_zero, eW_eq]

theorem wsEp_succ (n : ℕ) : wsEp (n + 1) = eN (wsEp n) := by
  rw [wsEp, wsEp, go_eN_veb, Nat.cast_succ]; simp only [add_assoc]

theorem ws_nat_lt_Om1 (n : ℕ) : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1

theorem wsEp_lt_Lw (n : ℕ) : wsEp n < wsLw := by
  refine (veblen_lt_veblen_iff_right).2 ?_
  rw [add_assoc]
  exact (add_lt_add_iff_left Om1).2 (by
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _)

theorem wsLw_lt_G : wsLw < gcG 0 :=
  gl_veb_lt_G0 gl_one_lt_G0 ((inE_indec gl_G0_E).add_lt gl_Om1_lt_G0 (omega0_lt_inE gl_G0_E))

theorem wsEp_mono (n : ℕ) : wsEp n < wsEp (n + 1) := by
  rw [wsEp_succ]; exact lt_eN _

theorem wsEp_E (n : ℕ) : InE (wsEp n) := luP_E le_rfl (luP_veblen 1 _)

theorem wsLw_E : InE wsLw := luP_E le_rfl (luP_veblen 1 _)

theorem wsEp_Om1 (n : ℕ) : Om1 < wsEp n := by
  induction n with
  | zero => rw [wsEp_zero]; exact Om1_lt_eW
  | succ n ih => exact ih.trans (wsEp_mono n)

theorem ws_not_glFw (n : ℕ) : ¬ glFw 1 (n : Ordinal.{0}) := by
  rintro ⟨f, hf, m, hm⟩
  have h1 : Om1 < (n : Ordinal.{0}) := hf.2.trans_le (by rw [hm]; exact le_self_add)
  exact absurd h1 (not_lt.2 (ws_nat_lt_Om1 n).le)

theorem wsEp_psi (n : ℕ) : glPsi 1 (n : Ordinal.{0}) = wsEp n := by
  rw [glPsi, glLam_of_not (ws_not_glFw n), glY0_lt wh_one_lt_Om1, wsEp, add_assoc Om1, add_assoc Om1]
  congr 2
  rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]

theorem wsEp_lt_G (n : ℕ) : wsEp n < gcG 0 := (wsEp_lt_Lw n).trans wsLw_lt_G

theorem wsEp_gate (n : ℕ) : glQE (wsEp n) = 0 := by
  have hn : (n : Ordinal.{0}) < gcG 0 := (ws_nat_lt_Om1 n).trans gl_Om1_lt_G0
  rw [← glG_base (wsEp_E n) (wsEp_Om1 n) (wsEp_lt_G n), ← wsEp_psi n, glG_psi le_rfl gl_one_lt_G0 hn, glQ_one,
    glQ_nat, max_self]

/-- **THE BASES `ε_{Ω₁+1+n}`**, every `n`. -/
theorem ws_base_ep : ∀ n : ℕ, BCls ML (wsEp n)
  | 0 => by rw [wsEp_zero]; exact ws_base_E
  | n + 1 => by
    rw [wsEp_succ]
    refine ws_base_succ (wsEp_E n) (wsEp_Om1 n) (by rw [← wsEp_succ]; exact wsEp_lt_G (n + 1)) ?_
    rw [wsEp_gate, max_eq_left zero_le]; exact one_le_gh _

/-- **THE BASE `ε_{Ω₁+ω}`**: the `ω`-sequence `ε_{Ω₁+1+n}`. -/
theorem ws_base_top : BCls ML wsLw := by
  refine Or.inl ⟨wsEp, fun n => ⟨(wsEp_Om1 n).le, wp_Om1_dvd_E (wsEp_E n) (wsEp_Om1 n)⟩, wsEp_mono, wsEp_lt_Lw,
    fun t ht => ?_, fun n => ?_⟩
  · have hlim : IsSuccLimit (Om1 + ω) := Ordinal.isSuccLimit_add _ isSuccLimit_omega0
    obtain ⟨y, hy, hty⟩ := ((isNormal_veblen 1).lt_iff_exists_lt hlim).1 ht
    rcases lt_or_ge y Om1 with hyO | hyO
    · refine ⟨0, hty.trans ((veblen_lt_veblen_iff_right).2 ?_)⟩
      rw [Nat.cast_zero, add_zero]; exact hyO.trans (lt_add_one _)
    · obtain ⟨m, rfl⟩ := exists_add_of_le hyO
      obtain ⟨n, rfl⟩ := lt_omega0.1 ((add_lt_add_iff_left Om1).1 hy)
      exact ⟨n, hty.trans ((veblen_lt_veblen_iff_right).2 (lt_add_one _))⟩
  · show max 1 (glG (wsEp n)) ≤ gh wsLw
    rw [glG_base (wsEp_E n) (wsEp_Om1 n) (wsEp_lt_G n), wsEp_gate, max_eq_left zero_le]; exact one_le_gh _

/-- **EVERY `ε`-NUMBER CODE IN `[ε_{Ω₁+1}, ε_{Ω₁+ω}]` HAS A SEQUENCE OF LEVELS** (UNCONDITIONAL). -/
theorem ws_base_w : WsBase (wsLw + 1) := by
  intro e he hEe hel
  have hle : e ≤ wsLw := Order.lt_add_one_iff.1 hel
  obtain ⟨y, rfl⟩ : e ∈ Set.range (veblen 1) := (mem_range_veblen one_ne_zero).2 fun b hb => by
    rw [lt_one_iff_zero.1 hb, veblen_zero_apply]; exact he
  have hy1 : Om1 + 1 ≤ y := by rw [eW_eq] at hEe; exact (veblen_le_veblen_iff_right).1 hEe
  have hyw : y ≤ Om1 + ω := (veblen_le_veblen_iff_right).1 hle
  rcases hyw.lt_or_eq with hyw | rfl
  · obtain ⟨m, rfl⟩ := exists_add_of_le (le_self_add.trans hy1 : Om1 ≤ y)
    have hm1 : 1 ≤ m := (add_le_add_iff_left Om1).1 hy1
    obtain ⟨n, rfl⟩ := lt_omega0.1 ((add_lt_add_iff_left Om1).1 hyw)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      have : 1 ≤ n := by exact_mod_cast hm1
      omega⟩
    have e : veblen 1 (Om1 + ((n' + 1 : ℕ) : Ordinal.{0})) = wsEp n' := by rw [wsEp, Nat.cast_succ, add_assoc]
    rw [e]; exact ws_base_ep n'
  · exact ws_base_top

/-- **THE (A2) CLASSIFICATION UP TO `ε_{Ω₁+ω}`** (UNCONDITIONAL). -/
theorem wsCls_w : WsCls wsA2 (wsLw + 1) :=
  wsCls_of_base (Order.add_one_le_of_lt wsLw_lt_G) ws_base_w

end Googology.Trans.PoR.InaccPsi.R2.Ws
