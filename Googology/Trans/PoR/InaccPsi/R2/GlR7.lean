import Googology.Trans.PoR.InaccPsi.R2.GlR6

/-!
# CODES BELOW `Γ_{Ω₁+1}`: the last term of a limit code, with Lemma EXACT for its logend

For every limit code `c < Γ_{Ω₁+1}` the reading splits as `c(x) = l'(x) + ω^{T(x)}` with `ω^{T(x)} ∣ l'(x)`,
`l'(x) ≤ c'(x)` for a code `c' < c` (gate at most that of `c`), and the logend `T` has LEMMA EXACT at every pair of
bases above the gate (`GlLD`).  The new case against round 82 is an `ε`-number code `c = glPsi α η` of ANY level
(the code `ζ_{Ω₁+1}` included): `c(x) = 0 + ω^{c(x)}`, the logend is the reading itself (EXACT by `gl_pi`).  Lemma
IMG for the logend is `glPkgG_of_ex` (`R2.GlIm`, every value below `Γ_{ρ+1}`), used in `R2.GlR8`.

* `GlLD`, `gl_ld_low`, `gl_ld_eps` (**the `ε`-number codes of every level**), `gl_ld` (**the induction**).

No new axiom.  New definition: `GlLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **The last term of a limit code `c`** with Lemma EXACT for its logend. -/
def GlLD (c : Ordinal.{0}) : Prop :=
  ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ glG cp ≤ glG c ∧
    (∀ x, InE x → x < Om1 → glG c < x →
      glR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ glR cp x) ∧
    ∀ σ ρ, Bases σ ρ → glG c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

/-- A limit code below `ε_{Ω₁+1}` (`rdc_lim_facts`, the term `tlg`). -/
theorem gl_ld_low {c : Ordinal.{0}} (hl : IsSuccLimit c) (hc : c < gfE) : GlLD c := by
  obtain ⟨a', l, d, ha', hga', hgl, hd, -, hF⟩ := rdc_lim_facts hl hc
  have ha'E : a' < gfE := ha'.trans hc
  refine ⟨a', fun x => rdc a' x, fun x => OT.ev (tlg l d) x, ha', by rw [glG_low hc, glG_low ha'E]; exact hga',
    fun x hx _ hg => ?_, fun σ ρ hB hg => ?_⟩
  · rw [glG_low hc] at hg
    obtain ⟨e1, e2, e3, -, -, e6⟩ := hF x hx hg
    beta_reduce
    rw [glR_low hc, glR_low ha'E, ← e3]
    exact ⟨e1, e2, (Gc.gc_lg_pos e6).ne', le_rfl⟩
  · rw [glG_low hc] at hg
    exact pi_ev hB _ (cb_tlg hB.1.pos (hgl.trans_lt hg) (hd.trans_lt hg))

/-- **An `ε`-number code `c = glPsi k η` of any level**: `c(x) = 0 + ω^{c(x)}`, the logend is the reading itself. -/
theorem gl_ld_eps {c : Ordinal.{0}} (hcI : InE c) (hOc : Om1 < c) (hc : c < gcG 0) : GlLD c := by
  refine ⟨0, fun _ => 0, fun x => glR c x, hcI.pos, by rw [glG_zero]; exact zero_le, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => gl_pi hB c hc hg⟩
  have hRE := (gl_eps_read hx hx1 hcI hOc hc hg).2.2.2.2.2.2.2.2.2.2.2.1
  beta_reduce
  rw [zero_add, show ω ^ glR c x = glR c x from hRE, glR_zero]
  exact ⟨rfl, dvd_zero _, hRE.pos.ne', le_rfl⟩

/-- **THE LAST TERM OF EVERY LIMIT CODE below `Γ_{Ω₁+1}`**, with Lemma EXACT for its logend. -/
theorem gl_ld : ∀ c, IsSuccLimit c → c < gcG 0 → GlLD c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc
  rcases lt_or_ge c gfE with hcE | hcE
  · exact gl_ld_low hl hcE
  by_cases hcI : InE c
  · exact gl_ld_eps hcI (Om1_lt_eW.trans_le hcE) hc
  have hEc' := gl_E_lt_self hcE hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE
  set E := guE c with hEdef
  have hEcE : InE E := guE_E c
  have hOE : Om1 < E := gl_Om1_lt_E hcE
  have hEB : E < gcG 0 := hEc'.trans hc
  have hcN' : c < eN E := gl_lt_eN hcE
  have hkN : log E c < eN E := hkc.trans hcN'
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hgc : glG c = max (max (glQE E) (glQ k)) (max (glQ d) (glG r)) := glG_dec hcE hc
  have hRc : ∀ x, glR c x = glR E x ^ glR k x * glR d x + glR r x := fun x => by
    rw [glR_dec hcE hc, ← gl_At_eq hcE hc]
  have hk0 : (0 : Ordinal.{0}) < E ^ k := opow_pos _ hEcE.pos
  have hcnf : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      E ^ k * b + t < eN E ∧ E ^ k * b + t < gcG 0 := fun b t _ _ _ h =>
    ⟨h.trans_lt hcN', h.trans_lt hc⟩
  have hRp : ∀ b t x, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      glR (E ^ k * b + t) x = glR E x ^ glR k x * glR b x + glR t x := fun b t x hb hbE ht h => by
    rw [glR_cnf hEcE hOE hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2 x,
      ← glR_base hEcE hOE hEB]
  have hGp : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      glG (E ^ k * b + t) = max (max (glQE E) (glQ k)) (max (glQ b) (glG t)) := fun b t hb hbE ht h =>
    glG_cnf hEcE hOE hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2
  have hgx : ∀ x, ω < x → glG c < x → glG (glI E) < x ∧ glG k < x ∧ glG d < x ∧ glG r < x :=
    fun x hωx h => gl_parts_g hωx hcE hc h
  have hBE : ∀ x, InE x → x < Om1 → glG c < x → InE (glR E x) := fun x hx hx1 hg =>
    (gl_eps_read hx hx1 hEcE hOE hEB (gl_E_g hcE hc hg)).2.2.2.2.2.2.2.2.2.2.2.1
  have hKpos : ∀ x, InE x → x < Om1 → glG c < x → 0 < glR k x := fun x hx hx1 hg =>
    glR_pos hx hx1 hk (hkc.trans hc) (hgx x (omega0_lt_inE hx) hg).2.1
  -- the logend `B·K` and its Lemma EXACT
  have hBKex : ∀ σ ρ, Bases σ ρ → glG c < σ →
      glR E ρ * glR k ρ ∈ TB ρ σ ∧ pi σ ρ (glR E ρ * glR k ρ) = glR E σ * glR k σ := by
    intro σ ρ hB hg
    obtain ⟨g0n, g0k, -, -⟩ := hgx σ (omega0_lt_inE hB.1) hg
    have hgE : glG E < σ := gl_E_g hcE hc hg
    have hexE := gl_pi hB E hEB hgE
    refine gl_BK_pi hB hEcE hOE hEB hgE hk hkN g0k hexE (fun hω => ?_)
    obtain ⟨-, hB', hg', -⟩ := gl_mulE hEcE hOE hEB k hk hkN
    have hgq : glQE E < σ := by have := gl_E_g hcE hc hg; rwa [glG_base hEcE hOE hEB] at this
    exact gl_pi hB _ hB' (hg'.trans_lt (max_lt hgq g0k))
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hcd : c = E ^ k * d := by rw [← hdec, hr0, add_zero]
    have hRc0 : ∀ x, glR c x = glR E x ^ glR k x * glR d x := fun x => by
      rw [hRc, hr0, glR_zero, add_zero]
    have hgc0 : glG c = max (max (glQE E) (glQ k)) (glQ d) := by
      rw [hgc, hr0, glG_zero, max_eq_left zero_le]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `B·K`
      rw [succ_eq_add_one] at hsucc
      have hd'd : d' < d := by rw [← hsucc]; exact lt_add_one d'
      have hd'E : d' < E := hd'd.trans hdE
      have hdB : d' + 1 < gcG 0 := by rw [hsucc]; exact hdc.trans hc
      refine ⟨if d' = 0 then 0 else E ^ k * d' + 0, fun x => glR E x ^ glR k x * glR d' x,
        fun x => glR E x * glR k x, ?_, ?_, fun x hx hx1 hg => ?_, hBKex⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (lt_of_lt_of_le eW_E.pos hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hd'd
      · split_ifs with h0
        · rw [glG_zero]; exact zero_le
        · have hle : E ^ k * d' + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _
          rw [hGp d' 0 h0 hd'E hk0 hle, glG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          refine max_le_max le_rfl ?_
          unfold glQ
          by_cases hω : d' < ω
          · rw [if_pos hω]; exact zero_le
          · rw [if_neg hω, if_neg (fun h => hω ((lt_add_one d').trans h))]
            exact glG_le_succ d' hdB
      · have hB := hBE x hx hx1 hg
        beta_reduce
        refine ⟨?_, gu_dvd hB le_rfl, (mul_pos hB.pos (hKpos x hx hx1 hg)).ne', ?_⟩
        · rw [hRc0, ← hsucc, glR_succ d' hdB, mul_add_one, gu_pow_eq hB]
        · split_ifs with h0
          · rw [h0, glR_zero, mul_zero]
          · rw [hRp d' 0 x h0 hd'E hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _), glR_zero,
              add_zero]
    · -- `d` a limit: the logend is `B·K + T_d`
      obtain ⟨cd, lpd, Td, hcdd, hgcd, hdd, hexd⟩ := IH d hdc hdl (hdc.trans hc)
      have hdω : ω ≤ d := omega0_le_of_isSuccLimit hdl
      have hQd : glQ d = glG d := by unfold glQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, glG c < x → glG d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcdE : cd < E := hcdd.trans hdE
      refine ⟨if cd = 0 then 0 else E ^ k * cd + 0, fun x => glR E x ^ glR k x * lpd x,
        fun x => glR E x * glR k x + Td x, ?_, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (lt_of_lt_of_le eW_E.pos hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hcdd
      · split_ifs with h0
        · rw [glG_zero]; exact zero_le
        · have hle : E ^ k * cd + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _
          rw [hGp cd 0 h0 hcdE hk0 hle, glG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((glQ_le cd).trans hgcd)
      · have hB := hBE x hx hx1 hg
        obtain ⟨e1, e2, e3, e4⟩ := hdd x hx hx1 (hgd x hg)
        beta_reduce
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hRc0, e1, mul_add, gu_pow_eq hB, ← opow_add]
        · obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gu_pow_eq hB, ← opow_add]⟩
        · exact (lt_of_lt_of_le (mul_pos hB.pos (hKpos x hx hx1 hg)) le_self_add).ne'
        · split_ifs with h0
          · rw [h0, glR_zero] at e4
            rw [nonpos_iff_eq_zero.1 e4, mul_zero, glR_zero]
          · rw [hRp cd 0 x h0 hcdE hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _), glR_zero,
              add_zero]
            exact mul_le_mul_right e4 _
      · obtain ⟨a1, a2⟩ := hBKex σ ρ hB hg
        obtain ⟨b1, b2⟩ := hexd σ ρ hB (hgd σ hg)
        obtain ⟨c1, c2⟩ := pi_add hB a1 b1
        exact ⟨c1, by rw [c2, a2, b2]⟩
  · -- `r ≠ 0`: `r` a limit, the last term of `r`
    have hrl : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hsucc⟩ | hrl
      · exact absurd h0 hr0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (E ^ k * d + r') := by rw [← hdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hrl
    have hgr : ∀ x, glG c < x → glG r < x := fun x h => (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt (hgc ▸ h))
    have hrB : r < gcG 0 := hrc.trans hc
    obtain ⟨cr, lpr, Tr, hcrr, hgcr, hdr, hexr⟩ := IH r hrc hrl hrB
    have hcrk : cr < E ^ k := hcrr.trans hr
    have hle : E ^ k * d + cr ≤ c := by rw [← hdec]; exact add_le_add le_rfl hcrr.le
    refine ⟨E ^ k * d + cr, fun x => glR E x ^ glR k x * glR d x + lpr x, Tr, ?_, ?_,
      fun x hx hx1 hg => ?_, fun σ ρ hB hg => hexr σ ρ hB (hgr σ hg)⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hcrr
    · rw [hGp d cr hd0 hdE hcrk hle, hgc]; exact max_le_max le_rfl (max_le_max le_rfl hgcr)
    · have hB := hBE x hx hx1 hg
      obtain ⟨e1, e2, e3, e4⟩ := hdr x hx hx1 (hgr x hg)
      beta_reduce
      have hωx := omega0_lt_inE hx
      obtain ⟨-, g0k, -, g0r⟩ := hgx x hωx hg
      have hgE : glG E < x := gl_E_g hcE hc hg
      -- the logend of `r(x)` lies below `B·K`
      have hTle : Tr x ≤ glR E x * glR k x := by
        have hb := gl_bound_of hx hx1 (fun j hj => (gl_mono_top hx hx1 j hj).1)
          (fun j hj => (gl_mono_top hx hx1 j hj).2) hEcE hOE hEB hgE (gl_mono_top hx hx1 E hEB).1
          r hrB hrB g0r (hrc.trans hcN') k hk (hkc.trans hc) (hkc.trans hc) g0k hr
        rw [gu_pow_eq hB] at hb
        have h1 : ω ^ Tr x ≤ glR r x := by rw [e1]; exact le_add_self
        exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
      refine ⟨by rw [hRc, e1, add_assoc], Ge.dvd_add' (gu_dvd hB hTle) e2, e3, ?_⟩
      rw [hRp d cr x hd0 hdE hcrk hle]
      exact add_le_add le_rfl e4

end Googology.Trans.PoR.InaccPsi.R2.Gl
