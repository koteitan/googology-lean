import Googology.Trans.PoR.InaccPsi.R2.WsZeta
import Googology.Trans.PoR.InaccPsi.R2.TaVeb

/-!
# WxVeb: THE ARGUMENTS AND GATES OF A VEBLEN NODE `glPsi α η` AT EVERY LEVEL `α < Γ_{Ω₁+1}`

Generic in the level `α` (no per-level port):

* `wx_lam_ge` (`y₀(α) + η ≤ Λ_α(η)`), `wx_lam_succ` (**`Λ_α(η+1) = Λ_α(η) + 1`**), `wx_fw_lim` (a limit `η` with
  `glFw α η` is a fixed point of `φ_α` above `Ω₁`);
* `wx_psi_cont` (**continuity of `glPsi α` at a limit index `η` with `¬ glFw α η`**);
* the codes of the arguments met by the sequences: `wx_veb_F` (`φ(β, f+1) = glPsi β f`, `f ∈ F_β`),
  `wx_veb_Om_lt` / `wx_veb_Om_ge` (`φ(β, Ω₁+1)`), `wx_veb_psi` (`φ(β, c) = glPsi β c`, `c` an `ε`-number above `Ω₁`
  that is not a fixed point of `φ_β`);
* gates: `wx_gh_psi` (`gh (glPsi α η) = max 1 (max (glQ α) (glQ η))`), `wx_glQ_Om1`, `wx_glQ_Om1s`, `wx_gh_veb`;
* levels: `wx_veb_lt_left` (`φ(β, f+1) < φ(β', f+1)` for `β < β'`), `wx_veb_lim_cof0` (at a limit level `a`, every
  `x < φ(a, 0)` is below some `φ(a', 0)`, `a' < a`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wx

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
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
open Googology.Trans.PoR.InaccPsi.R2.Wo Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Wp
open Googology.Trans.PoR.InaccPsi.R2.Gk
open Googology.Trans.PoR.InaccPsi.R2.Ws Googology.Trans.PoR.InaccPsi.R2.Ws.WsC

/-! ## The arguments `Λ_α` -/

theorem wx_lam_ge (α η : Ordinal.{0}) : glY0 α + η ≤ glLam α η := by
  by_cases h : glFw α η
  · obtain ⟨f, hf, n, hn⟩ := h
    rw [glLam_of ⟨f, hf, n, hn⟩, hn, ← add_assoc, gl_absorb_le (glF_E hf) hf.2 (le_refl f)]
    exact (lt_add_one _).le
  · rw [glLam_of_not h]

/-- A limit `η` with `glFw α η` is itself a fixed point of `φ_α` above `Ω₁`. -/
theorem wx_fw_lim {α η : Ordinal.{0}} (hl : IsSuccLimit η) (h : glFw α η) : glF α η := by
  obtain ⟨f, hf, n, hn⟩ := h
  cases n with
  | zero => rw [hn, Nat.cast_zero, add_zero]; exact hf
  | succ m =>
    exfalso
    have e : η = f + (m : Ordinal.{0}) + 1 := by rw [hn, Nat.cast_succ, add_assoc]
    rw [e] at hl
    exact absurd (hl.add_one_lt (lt_add_one (f + (m : Ordinal.{0})))) (lt_irrefl _)

theorem wx_fw_succ {α η : Ordinal.{0}} : glFw α (η + 1) ↔ glFw α η := by
  constructor
  · rintro ⟨f, hf, n, hn⟩
    cases n with
    | zero =>
      exfalso
      rw [Nat.cast_zero, add_zero] at hn
      have hlim := ev_isSuccLimit_of_inE (glF_E hf)
      rw [← hn] at hlim
      exact absurd (hlim.add_one_lt (lt_add_one η)) (lt_irrefl _)
    | succ m =>
      refine ⟨f, hf, m, ?_⟩
      rw [Nat.cast_succ, ← add_assoc] at hn
      exact Order.succ_injective (by rw [← Ordinal.add_one_eq_succ, ← Ordinal.add_one_eq_succ]; exact hn)
  · rintro ⟨f, hf, n, hn⟩
    exact ⟨f, hf, n + 1, by rw [hn, Nat.cast_succ, add_assoc]⟩

/-- **`Λ_α(η+1) = Λ_α(η) + 1`.** -/
theorem wx_lam_succ (α η : Ordinal.{0}) : glLam α (η + 1) = glLam α η + 1 := by
  by_cases h : glFw α η
  · rw [glLam_of (wx_fw_succ.2 h), glLam_of h]
  · rw [glLam_of_not (fun h' => h (wx_fw_succ.1 h')), glLam_of_not h, add_assoc]

/-- **Continuity of `glPsi α` at a limit index `η` with `¬ glFw α η`.** -/
theorem wx_psi_cont {α η t : Ordinal.{0}} (hl : IsSuccLimit η) (hnf : ¬ glFw α η) (ht : t < glPsi α η) :
    ∃ η', η' < η ∧ t < glPsi α η' := by
  unfold glPsi at ht
  rw [glLam_of_not hnf] at ht
  have hlim : IsSuccLimit (glY0 α + η) := Ordinal.isSuccLimit_add _ hl
  obtain ⟨y, hy, hty⟩ := ((isNormal_veblen α).lt_iff_exists_lt hlim).1 ht
  have hη0 : (0 : Ordinal.{0}) < η := pos_iff_ne_zero.2 hl.ne_bot
  rcases lt_or_ge y (glY0 α) with hy1 | hy1
  · refine ⟨0, hη0, hty.trans_le ?_⟩
    unfold glPsi
    exact (veblen_le_veblen_iff_right).2 (hy1.le.trans ((le_self_add).trans (wx_lam_ge α 0)))
  · obtain ⟨u, rfl⟩ := exists_add_of_le hy1
    have hu : u < η := (add_lt_add_iff_left _).1 hy
    exact ⟨u, hu, hty.trans_le ((veblen_le_veblen_iff_right).2 (wx_lam_ge α u))⟩

/-! ## The codes of the arguments -/

/-- `φ(β, f+1) = glPsi β f` for a fixed point `f ∈ F_β`. -/
theorem wx_veb_F {β f : Ordinal.{0}} (hf : glF β f) : veblen β (f + 1) = glPsi β f := by
  unfold glPsi; rw [glLam_of ⟨f, hf, 0, by rw [Nat.cast_zero, add_zero]⟩]

theorem wx_veb_Om_lt {β : Ordinal.{0}} (hβ : β < Om1) : veblen β (Om1 + 1) = glPsi β 0 := by
  unfold glPsi; rw [glLam_of_not (glFw_zero β), glY0_lt hβ, add_zero]

theorem wx_not_fw_Om1s (β : Ordinal.{0}) : ¬ glFw β (Om1 + 1) := by
  rintro ⟨f, hf, n, hn⟩
  have h1 : Om1 + 1 < f := (ev_isSuccLimit_of_inE (glF_E hf)).add_one_lt hf.2
  have h2 : f ≤ Om1 + 1 := by rw [hn]; exact le_self_add
  exact absurd (h1.trans_le h2) (lt_irrefl _)

theorem wx_veb_Om_ge {β : Ordinal.{0}} (hβ : Om1 ≤ β) : veblen β (Om1 + 1) = glPsi β (Om1 + 1) := by
  unfold glPsi
  rw [glLam_of_not (wx_not_fw_Om1s β)]
  rcases hβ.lt_or_eq with h | h
  · rw [glY0_gt h, zero_add]
  · rw [← h, glY0_eq, ← add_assoc, one_add_of_omega0_le omega_lt_Om1.le]

/-- `φ(β, c) = glPsi β c` for an `ε`-number `c > Ω₁` that is not a fixed point of `φ_β`. -/
theorem wx_veb_psi {β c : Ordinal.{0}} (hc : InE c) (hOc : Om1 < c) (hP : ¬ LuP (β + 1) c) :
    veblen β c = glPsi β c := by
  have hnf : ¬ glFw β c := fun h => hP (wx_fw_lim (ev_isSuccLimit_of_inE hc) h).1
  unfold glPsi; rw [glLam_of_not hnf, gl_absorb_le hc hOc le_rfl]

/-! ## Gates -/

theorem wx_gh_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 0) (hηG : η < gcG 0) :
    gh (glPsi α η) = max 1 (max (glQ α) (glQ η)) := by
  unfold gh; rw [glG_psi hα hαG hηG]

theorem wx_glQ_inf {a : Ordinal.{0}} (ha : ω ≤ a) : glQ a = glG a := if_neg (not_lt.2 ha)

theorem wx_glQ_Om1 : glQ Om1 = 1 := by
  rw [wx_glQ_inf omega_lt_Om1.le, glG_low Om1_lt_eW, (rdc_Om1 0).2]

theorem wx_Om1s_lt_E : Om1 + 1 < gfE := (ev_isSuccLimit_of_inE eW_E).add_one_lt Om1_lt_eW

theorem wx_glQ_Om1s : glQ (Om1 + 1) = 1 := by
  rw [wx_glQ_inf (omega_lt_Om1.le.trans le_self_add), glG_low wx_Om1s_lt_E]
  have h := rdc_cnf (l := 1) (q := 1) (r := 1) (gf_one_lt_Om1.trans Om1_lt_eW) one_ne_zero gf_one_lt_Om1
    (by rw [opow_one]; exact gf_one_lt_Om1) 0
  rw [opow_one, mul_one, (rdc_const gf_one_lt_Om1 0).2, max_self, max_self] at h
  exact h.2

theorem wx_Om1s_lt_G : Om1 + 1 < gcG 0 := gl_G0_lim.add_one_lt gl_Om1_lt_G0

/-- **The gate of `φ(β, f+1)`** for `f = Ω₁` or `f ∈ F_β`. -/
theorem wx_gh_veb {β f : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβG : β < gcG 0) (hfG : f < gcG 0)
    (hf : f = Om1 ∨ glF β f) : gh (veblen β (f + 1)) ≤ max 1 (max (glQ β) (glQ f)) := by
  rcases hf with rfl | hf
  · rcases lt_or_ge β Om1 with h | h
    · rw [wx_veb_Om_lt h, wx_gh_psi hβ1 hβG gl_G0_E.pos, glQ_zero, wx_glQ_Om1]
      exact max_le_max le_rfl (max_le_max le_rfl zero_le)
    · rw [wx_veb_Om_ge h, wx_gh_psi hβ1 hβG wx_Om1s_lt_G, wx_glQ_Om1s, wx_glQ_Om1]
  · rw [wx_veb_F hf, wx_gh_psi hβ1 hβG hfG]

/-! ## Levels -/

/-- A successor is never a fixed point of `φ_β`. -/
theorem wx_veb_succ_ne (β f : Ordinal.{0}) : veblen β (f + 1) ≠ f + 1 := by
  intro h
  have h0 : veblen 0 (f + 1) = f + 1 := veblen_eq_self_of_le zero_le h
  rw [veblen_zero_apply] at h0
  have hl : IsSuccLimit (f + 1) := ev_isSuccLimit_of_inE h0
  exact absurd (hl.add_one_lt (lt_add_one f)) (lt_irrefl _)

theorem wx_lt_veb_succ (β f : Ordinal.{0}) : f + 1 < veblen β (f + 1) :=
  lt_of_le_of_ne (right_le_veblen _ _) (wx_veb_succ_ne β f).symm

/-- **`φ(β, f+1) < φ(β', f+1)` for `β < β'`.** -/
theorem wx_veb_lt_left {β β' : Ordinal.{0}} (h : β < β') (f : Ordinal.{0}) :
    veblen β (f + 1) < veblen β' (f + 1) :=
  calc veblen β (f + 1) < veblen β (veblen β' (f + 1)) := (veblen_lt_veblen_iff_right).2 (wx_lt_veb_succ β' f)
    _ = veblen β' (f + 1) := veblen_veblen_of_lt h _

/-- At a limit level `a`: every `x < φ(a, 0)` lies below `φ(a', 0)` for some `a' < a`. -/
theorem wx_veb_lim_cof0 {a x : Ordinal.{0}} (ha : IsSuccLimit a) (hx : x < veblen a 0) :
    ∃ a', a' < a ∧ x < veblen a' 0 := by
  have ha0 : a ≠ 0 := ha.ne_bot
  have e : veblen a 0 = nfpFamily (fun b : Iio a => veblen b.1) 0 := by
    rw [veblen_of_ne_zero ha0, derivFamily_zero]
  rw [e] at hx
  obtain ⟨l, hl⟩ := lt_nfpFamily_iff.1 hx
  have key : ∀ l : List (Iio a), ∃ b, b < a ∧
      List.foldr (fun b : Iio a => veblen b.1) (0 : Ordinal.{0}) l ≤ veblen b 0 := by
    intro l
    induction l with
    | nil => exact ⟨0, pos_iff_ne_zero.2 ha0, zero_le⟩
    | cons c l ih =>
      obtain ⟨b, hb, hle⟩ := ih
      set m := max c.1 b with hm
      have hma : m < a := max_lt c.2 hb
      refine ⟨m + 1, ha.add_one_lt hma, ?_⟩
      show veblen c.1 (List.foldr (fun b : Iio a => veblen b.1) 0 l) ≤ veblen (m + 1) 0
      calc veblen c.1 (List.foldr (fun b : Iio a => veblen b.1) 0 l) ≤ veblen c.1 (veblen (m + 1) 0) :=
            (veblen_le_veblen_iff_right).2 (hle.trans (veblen_left_monotone 0
              ((le_max_right c.1 b).trans le_self_add)))
        _ = veblen (m + 1) 0 :=
            veblen_veblen_of_lt (Order.lt_add_one_iff.2 (le_max_left _ _)) 0
  obtain ⟨b, hb, hle⟩ := key l
  exact ⟨b, hb, hl.trans_le hle⟩

end Googology.Trans.PoR.InaccPsi.R2.Wx
