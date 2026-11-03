import Googology.Trans.PoR.InaccPsi.R2.YrGate
import Googology.Trans.PoR.InaccPsi.R2.YhLDN

/-!
# YrLDN: THE LAST TERM OF EVERY LIMIT CODE BELOW `B_Γ` (READ ATOM INDICES), with Lemma EXACT for its logend

`Yh.YhLDN` for the reading `Yr.yrR`: below `G` it is `Gl.gl_ld`; at an `ε`-number code `e ≥ G` the logend is the
reading itself (`Yr.yr_pi`); otherwise the bracket `c = e^k·d + r` and the argument of `Gl.gl_ld`.

* `YrLDN`, `yr_ldN_low`, `yr_ldN_eps`, `yr_ldN` (**every limit code below `B_Γ`**).

No new axiom.  New definition: `YrLDN`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Yh

/-- **The last term of a limit code `c`** (reading `yrR`) with Lemma EXACT for its logend. -/
def YrLDN (c : Ordinal.{0}) : Prop :=
  ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ yrG cp ≤ yrG c ∧
    (∀ x, InE x → x < Om1 → yrG c < x →
      yrR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ yrR cp x) ∧
    ∀ σ ρ, Bases σ ρ → yrG c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

/-- Below `G`: `Gl.gl_ld`. -/
theorem yr_ldN_low {c : Ordinal.{0}} (hl : IsSuccLimit c) (hc : c < gcG 0) : YrLDN c := by
  obtain ⟨cp, lp, T, hcp, hg, hdec, hex⟩ := gl_ld c hl hc
  have hcp0 : cp < gcG 0 := hcp.trans hc
  refine ⟨cp, lp, T, hcp, by rw [yrG_low hc, yrG_low hcp0]; exact hg, fun x hx hx1 hgx => ?_,
    fun σ ρ hB hgx => ?_⟩
  · rw [yrG_low hc] at hgx
    rw [yrR_low hc, yrR_low hcp0]
    exact hdec x hx hx1 hgx
  · rw [yrG_low hc] at hgx
    exact hex σ ρ hB hgx

/-- **An `ε`-number code `c ≥ G`** (a base atom or not): `c(x) = 0 + ω^{c(x)}`, the logend is the reading itself. -/
theorem yr_ldN_eps {c : Ordinal.{0}} (hcI : InE c) (hG : gcG 0 ≤ c) (hc : c < Tf.tfBG) :
    YrLDN c := by
  refine ⟨0, fun _ => 0, fun x => yrR c x, hcI.pos, by rw [yrG_zero]; exact zero_le, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => yr_pi hB c hc hg⟩
  have hRE : InE (yrR c x) := by rw [yrR_base hcI hG]; exact (yrA_facts hx hx1 hcI hG hc hg).1
  beta_reduce
  rw [zero_add, show ω ^ yrR c x = yrR c x from hRE, yrR_zero]
  exact ⟨rfl, dvd_zero _, hRE.pos.ne', le_rfl⟩

/-- **THE LAST TERM OF EVERY LIMIT CODE below `B_Γ`**, with Lemma EXACT for its logend. -/
theorem yr_ldN : ∀ c, IsSuccLimit c → c < Tf.tfBG → YrLDN c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc
  rcases lt_or_ge c (gcG 0) with hct | hcE
  · exact yr_ldN_low hl hct
  by_cases hcI : InE c
  · exact yr_ldN_eps hcI hcE hc
  have hcE' : gfE ≤ c := yh_gfE_le hcE
  have hEc' := gl_E_lt_self hcE' hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE'
  set E := guE c with hEdef
  have hEcE : InE E := guE_E c
  have hEt : gcG 0 ≤ E := yh_G_le_E hcE
  have hEB : E < Tf.tfBG := hEc'.trans hc
  have hcN' : c < eN E := gl_lt_eN hcE'
  have hkN : log E c < eN E := hkc.trans hcN'
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hgc : yrG c = max (max (yrQE E) (yrQ k)) (max (yrQ d) (yrG r)) := yrG_dec hcE
  have hRc : ∀ x, yrR c x = yrR E x ^ yrR k x * yrR d x + yrR r x := fun x => by
    rw [yrR_dec hcE, ← yrR_base hEcE hEt]
  have hk0 : (0 : Ordinal.{0}) < E ^ k := opow_pos _ hEcE.pos
  have hcnf : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      E ^ k * b + t < eN E ∧ E ^ k * b + t < Tf.tfBG := fun b t _ _ _ h =>
    ⟨h.trans_lt hcN', h.trans_lt hc⟩
  have hRp : ∀ b t x, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      yrR (E ^ k * b + t) x = yrR E x ^ yrR k x * yrR b x + yrR t x := fun b t x hb hbE ht h => by
    rw [yrR_cnf hEcE hEt hk hb hbE ht (hcnf b t hb hbE ht h).1 x, ← yrR_base hEcE hEt]
  have hGp : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      yrG (E ^ k * b + t) = max (max (yrQE E) (yrQ k)) (max (yrQ b) (yrG t)) := fun b t hb hbE ht h =>
    yrG_cnf hEcE hEt hk hb hbE ht (hcnf b t hb hbE ht h).1
  have hgx : ∀ x, ω < x → yrG c < x → yrG k < x ∧ yrG d < x ∧ yrG r < x :=
    fun x hωx h => yr_parts_g hωx hcE h
  have hBE : ∀ x, InE x → x < Om1 → yrG c < x → InE (yrR E x) := fun x hx hx1 hg =>
    by rw [yrR_base hEcE hEt]; exact (yrA_facts hx hx1 hEcE hEt hEB (yr_E_g hcE hg)).1
  have hKpos : ∀ x, InE x → x < Om1 → yrG c < x → 0 < yrR k x := fun x hx hx1 hg =>
    yrR_pos hx hx1 hk (hkc.trans hc) (hgx x (omega0_lt_inE hx) hg).1
  -- the logend `B·K` and its Lemma EXACT
  have hBKex : ∀ σ ρ, Bases σ ρ → yrG c < σ →
      yrR E ρ * yrR k ρ ∈ TB ρ σ ∧ pi σ ρ (yrR E ρ * yrR k ρ) = yrR E σ * yrR k σ := by
    intro σ ρ hB hg
    obtain ⟨g0k, -, -⟩ := hgx σ (omega0_lt_inE hB.1) hg
    have hgE : yrG E < σ := yr_E_g hcE hg
    have hexE := yr_pi hB E hEB hgE
    refine yr_BK_pi hB hEcE hEt hEB hk hkN g0k hexE (fun _ => ?_)
    obtain ⟨-, hB', hg', -⟩ := yr_mulE hEcE hEt hEB k hk hkN
    have hgq : yrQE E < σ := by have := yr_E_g hcE hg; rwa [yrG_base hEcE hEt] at this
    exact yr_pi hB _ hB' (hg'.trans_lt (max_lt hgq g0k))
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hcd : c = E ^ k * d := by rw [← hdec, hr0, add_zero]
    have hRc0 : ∀ x, yrR c x = yrR E x ^ yrR k x * yrR d x := fun x => by
      rw [hRc, hr0, yrR_zero, add_zero]
    have hgc0 : yrG c = max (max (yrQE E) (yrQ k)) (yrQ d) := by
      rw [hgc, hr0, yrG_zero, max_eq_left zero_le]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `B·K`
      rw [succ_eq_add_one] at hsucc
      have hd'd : d' < d := by rw [← hsucc]; exact lt_add_one d'
      have hd'E : d' < E := hd'd.trans hdE
      have hdB : d' + 1 < Tf.tfBG := by rw [hsucc]; exact hdc.trans hc
      refine ⟨if d' = 0 then 0 else E ^ k * d' + 0, fun x => yrR E x ^ yrR k x * yrR d' x,
        fun x => yrR E x * yrR k x, ?_, ?_, fun x hx hx1 hg => ?_, hBKex⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (gl_G0_E.pos.trans_le hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hd'd
      · split_ifs with h0
        · rw [yrG_zero]; exact zero_le
        · have hle : E ^ k * d' + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _
          rw [hGp d' 0 h0 hd'E hk0 hle, yrG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          refine max_le_max le_rfl ?_
          unfold yrQ
          by_cases hω : d' < ω
          · rw [if_pos hω]; exact zero_le
          · rw [if_neg hω, if_neg (fun h => hω ((lt_add_one d').trans h))]
            exact yrG_le_succ d'
      · have hB := hBE x hx hx1 hg
        beta_reduce
        refine ⟨?_, gu_dvd hB le_rfl, (mul_pos hB.pos (hKpos x hx hx1 hg)).ne', ?_⟩
        · rw [hRc0, ← hsucc, yrR_succ d', mul_add_one, gu_pow_eq hB]
        · split_ifs with h0
          · rw [h0, yrR_zero, mul_zero]
          · rw [hRp d' 0 x h0 hd'E hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _), yrR_zero,
              add_zero]
    · -- `d` a limit: the logend is `B·K + T_d`
      obtain ⟨cd, lpd, Td, hcdd, hgcd, hdd, hexd⟩ := IH d hdc hdl (hdc.trans hc)
      have hdω : ω ≤ d := omega0_le_of_isSuccLimit hdl
      have hQd : yrQ d = yrG d := by unfold yrQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, yrG c < x → yrG d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcdE : cd < E := hcdd.trans hdE
      refine ⟨if cd = 0 then 0 else E ^ k * cd + 0, fun x => yrR E x ^ yrR k x * lpd x,
        fun x => yrR E x * yrR k x + Td x, ?_, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (gl_G0_E.pos.trans_le hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hcdd
      · split_ifs with h0
        · rw [yrG_zero]; exact zero_le
        · have hle : E ^ k * cd + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _
          rw [hGp cd 0 h0 hcdE hk0 hle, yrG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((yrQ_le cd).trans hgcd)
      · have hB := hBE x hx hx1 hg
        obtain ⟨e1, e2, e3, e4⟩ := hdd x hx hx1 (hgd x hg)
        beta_reduce
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hRc0, e1, mul_add, gu_pow_eq hB, ← opow_add]
        · obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gu_pow_eq hB, ← opow_add]⟩
        · exact (lt_of_lt_of_le (mul_pos hB.pos (hKpos x hx hx1 hg)) le_self_add).ne'
        · split_ifs with h0
          · rw [h0, yrR_zero] at e4
            rw [nonpos_iff_eq_zero.1 e4, mul_zero, yrR_zero]
          · rw [hRp cd 0 x h0 hcdE hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _), yrR_zero,
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
    have hgr : ∀ x, yrG c < x → yrG r < x := fun x h => (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt (hgc ▸ h))
    have hrB : r < Tf.tfBG := hrc.trans hc
    obtain ⟨cr, lpr, Tr, hcrr, hgcr, hdr, hexr⟩ := IH r hrc hrl hrB
    have hcrk : cr < E ^ k := hcrr.trans hr
    have hle : E ^ k * d + cr ≤ c := by rw [← hdec]; exact add_le_add le_rfl hcrr.le
    refine ⟨E ^ k * d + cr, fun x => yrR E x ^ yrR k x * yrR d x + lpr x, Tr, ?_, ?_,
      fun x hx hx1 hg => ?_, fun σ ρ hB hg => hexr σ ρ hB (hgr σ hg)⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hcrr
    · rw [hGp d cr hd0 hdE hcrk hle, hgc]; exact max_le_max le_rfl (max_le_max le_rfl hgcr)
    · have hB := hBE x hx hx1 hg
      obtain ⟨e1, e2, e3, e4⟩ := hdr x hx hx1 (hgr x hg)
      beta_reduce
      have hωx := omega0_lt_inE hx
      obtain ⟨g0k, -, g0r⟩ := hgx x hωx hg
      have hgE : yrG E < x := yr_E_g hcE hg
      -- the logend of `r(x)` lies below `B·K`
      have hTle : Tr x ≤ yrR E x * yrR k x := by
        have hb := yr_bound_of hx hx1 (fun j hj => (yr_mono_top hx hx1 j hj).1)
          (fun j hj => (yr_mono_top hx hx1 j hj).2) hEcE hEt hEB hgE (yr_mono_top hx hx1 E hEB).1
          r hrB hrB g0r (hrc.trans hcN') k hk (hkc.trans hc) (hkc.trans hc) g0k hr
        rw [gu_pow_eq hB] at hb
        have h1 : ω ^ Tr x ≤ yrR r x := by rw [e1]; exact le_add_self
        exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
      refine ⟨by rw [hRc, e1, add_assoc], Ge.dvd_add' (gu_dvd hB hTle) e2, e3, ?_⟩
      rw [hRp d cr x hd0 hdE hcrk hle]
      exact add_le_add le_rfl e4

end Googology.Trans.PoR.InaccPsi.R2.Yr
