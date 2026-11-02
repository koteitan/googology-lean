import Googology.Trans.PoR.InaccPsi.R2.XuC

/-!
# YhLD: THE LAST TERM OF EVERY LIMIT CODE BELOW `Γ(1)`, with Lemma EXACT for its logend

For every limit code `c < Γ(1)` the reading `Xu.xuR` splits as `c(x) = l'(x) + ω^{T(x)}` with `ω^{T(x)} ∣ l'(x)`,
`l'(x) ≤ c'(x)` for a code `c' < c` (gate at most that of `c`), and the logend `T` has Lemma EXACT at every pair of
bases above the gate (`YhLD`).  Below `t₀` it is the field `ld` of the hereditary step `Wt.wtD`; at an `ε`-number code
`e ≥ t₀` the logend is the reading itself (`Xu.xu_pi`); otherwise the bracket `c = e^k·d + r` and the argument of
`Gl.gl_ld` with the brackets `e ≥ t₀` (`Xu.xu_mulE`, `Xu.xu_BK_pi`, `Xu.xu_bound_of`).

* `YhLD`, `yh_ld_low`, `yh_ld_eps`, `yh_ld` (**the induction: every limit code below `Γ(1)`**).

No new axiom.  New definition: `YhLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu

/-- **The last term of a limit code `c < Γ(1)`** with Lemma EXACT for its logend. -/
def YhLD (c : Ordinal.{0}) : Prop :=
  ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ xuG cp ≤ xuG c ∧
    (∀ x, InE x → x < Om1 → xuG c < x →
      xuR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ xuR cp x) ∧
    ∀ σ ρ, Bases σ ρ → xuG c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

/-- Below `t₀`: the field `ld` of `Wt.wtD`. -/
theorem yh_ld_low {c : Ordinal.{0}} (hl : IsSuccLimit c) (hc : c < Wj.wjT 0) : YhLD c := by
  obtain ⟨cp, lp, T, hcp, hg, hdec, hex⟩ := wtD.ld c hl (by rw [wtD_B]; exact hc)
  have hcp0 : cp < Wj.wjT 0 := hcp.trans hc
  refine ⟨cp, lp, T, hcp, by rw [xuG_low hc, xuG_low hcp0]; exact hg, fun x hx hx1 hgx => ?_,
    fun σ ρ hB hgx => ?_⟩
  · rw [xuG_low hc] at hgx
    rw [xuR_low hc, xuR_low hcp0]
    exact hdec x hx hx1 hgx
  · rw [xuG_low hc] at hgx
    exact hex σ ρ hB hgx

/-- **An `ε`-number code `c ≥ t₀`**: `c(x) = 0 + ω^{c(x)}`, the logend is the reading itself. -/
theorem yh_ld_eps {c : Ordinal.{0}} (hcI : InE c) (ht : Wj.wjT 0 ≤ c) (hc : c < gcG 1) : YhLD c := by
  refine ⟨0, fun _ => 0, fun x => xuR c x, hcI.pos, by rw [xuG_zero]; exact zero_le, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => xu_pi hB c hc hg⟩
  have hRE := (xu_eps_read hx hx1 hcI ht hc hg).2.2.2.2.2.2.2.2.2.2.2.1
  beta_reduce
  rw [zero_add, show ω ^ xuR c x = xuR c x from hRE, xuR_zero]
  exact ⟨rfl, dvd_zero _, hRE.pos.ne', le_rfl⟩

/-- **THE LAST TERM OF EVERY LIMIT CODE below `Γ(1)`**, with Lemma EXACT for its logend. -/
theorem yh_ld : ∀ c, IsSuccLimit c → c < gcG 1 → YhLD c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc
  rcases lt_or_ge c (Wj.wjT 0) with hct | hcE
  · exact yh_ld_low hl hct
  by_cases hcI : InE c
  · exact yh_ld_eps hcI hcE hc
  have hcE' : gfE ≤ c := xu_gfE_le hcE
  have hEc' := gl_E_lt_self hcE' hcI
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gl_parts hcE'
  set E := guE c with hEdef
  have hEcE : InE E := guE_E c
  have hEt : Wj.wjT 0 ≤ E := xu_E_ge hcE
  have hEB : E < gcG 1 := hEc'.trans hc
  have hcN' : c < eN E := gl_lt_eN hcE'
  have hkN : log E c < eN E := hkc.trans hcN'
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hgc : xuG c = max (max (xuQE E) (xuQ k)) (max (xuQ d) (xuG r)) := xuG_dec hcE hc
  have hRc : ∀ x, xuR c x = xuR E x ^ xuR k x * xuR d x + xuR r x := fun x => by
    rw [xuR_dec hcE hc, ← xu_At_eq hcE hc]
  have hk0 : (0 : Ordinal.{0}) < E ^ k := opow_pos _ hEcE.pos
  have hcnf : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      E ^ k * b + t < eN E ∧ E ^ k * b + t < gcG 1 := fun b t _ _ _ h =>
    ⟨h.trans_lt hcN', h.trans_lt hc⟩
  have hRp : ∀ b t x, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      xuR (E ^ k * b + t) x = xuR E x ^ xuR k x * xuR b x + xuR t x := fun b t x hb hbE ht h => by
    rw [xuR_cnf hEcE hEt hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2 x,
      ← xuR_base hEcE hEt hEB]
  have hGp : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      xuG (E ^ k * b + t) = max (max (xuQE E) (xuQ k)) (max (xuQ b) (xuG t)) := fun b t hb hbE ht h =>
    xuG_cnf hEcE hEt hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2
  have hgx : ∀ x, ω < x → xuG c < x → xuG (xuI E) < x ∧ xuG k < x ∧ xuG d < x ∧ xuG r < x :=
    fun x hωx h => xu_parts_g hωx hcE hc h
  have hBE : ∀ x, InE x → x < Om1 → xuG c < x → InE (xuR E x) := fun x hx hx1 hg =>
    (xu_eps_read hx hx1 hEcE hEt hEB (xu_E_g hcE hc hg)).2.2.2.2.2.2.2.2.2.2.2.1
  have hKpos : ∀ x, InE x → x < Om1 → xuG c < x → 0 < xuR k x := fun x hx hx1 hg =>
    xuR_pos hx hx1 hk (hkc.trans hc) (hgx x (omega0_lt_inE hx) hg).2.1
  -- the logend `B·K` and its Lemma EXACT
  have hBKex : ∀ σ ρ, Bases σ ρ → xuG c < σ →
      xuR E ρ * xuR k ρ ∈ TB ρ σ ∧ pi σ ρ (xuR E ρ * xuR k ρ) = xuR E σ * xuR k σ := by
    intro σ ρ hB hg
    obtain ⟨g0n, g0k, -, -⟩ := hgx σ (omega0_lt_inE hB.1) hg
    have hgE : xuG E < σ := xu_E_g hcE hc hg
    have hexE := xu_pi hB E hEB hgE
    refine xu_BK_pi hB hEcE hEt hEB hgE hk hkN g0k hexE (fun _ => ?_)
    obtain ⟨-, hB', hg', -⟩ := xu_mulE hEcE hEt hEB k hk hkN
    have hgq : xuQE E < σ := by have := xu_E_g hcE hc hg; rwa [xuG_base hEcE hEt hEB] at this
    exact xu_pi hB _ hB' (hg'.trans_lt (max_lt hgq g0k))
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hcd : c = E ^ k * d := by rw [← hdec, hr0, add_zero]
    have hRc0 : ∀ x, xuR c x = xuR E x ^ xuR k x * xuR d x := fun x => by
      rw [hRc, hr0, xuR_zero, add_zero]
    have hgc0 : xuG c = max (max (xuQE E) (xuQ k)) (xuQ d) := by
      rw [hgc, hr0, xuG_zero, max_eq_left zero_le]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `B·K`
      rw [succ_eq_add_one] at hsucc
      have hd'd : d' < d := by rw [← hsucc]; exact lt_add_one d'
      have hd'E : d' < E := hd'd.trans hdE
      have hdB : d' + 1 < gcG 1 := by rw [hsucc]; exact hdc.trans hc
      refine ⟨if d' = 0 then 0 else E ^ k * d' + 0, fun x => xuR E x ^ xuR k x * xuR d' x,
        fun x => xuR E x * xuR k x, ?_, ?_, fun x hx hx1 hg => ?_, hBKex⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (xu_t0_E.pos.trans_le hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hd'd
      · split_ifs with h0
        · rw [xuG_zero]; exact zero_le
        · have hle : E ^ k * d' + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _
          rw [hGp d' 0 h0 hd'E hk0 hle, xuG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          refine max_le_max le_rfl ?_
          unfold xuQ
          by_cases hω : d' < ω
          · rw [if_pos hω]; exact zero_le
          · rw [if_neg hω, if_neg (fun h => hω ((lt_add_one d').trans h))]
            exact xuG_le_succ d' hdB
      · have hB := hBE x hx hx1 hg
        beta_reduce
        refine ⟨?_, gu_dvd hB le_rfl, (mul_pos hB.pos (hKpos x hx hx1 hg)).ne', ?_⟩
        · rw [hRc0, ← hsucc, xuR_succ d' hdB, mul_add_one, gu_pow_eq hB]
        · split_ifs with h0
          · rw [h0, xuR_zero, mul_zero]
          · rw [hRp d' 0 x h0 hd'E hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _), xuR_zero,
              add_zero]
    · -- `d` a limit: the logend is `B·K + T_d`
      obtain ⟨cd, lpd, Td, hcdd, hgcd, hdd, hexd⟩ := IH d hdc hdl (hdc.trans hc)
      have hdω : ω ≤ d := omega0_le_of_isSuccLimit hdl
      have hQd : xuQ d = xuG d := by unfold xuQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, xuG c < x → xuG d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcdE : cd < E := hcdd.trans hdE
      refine ⟨if cd = 0 then 0 else E ^ k * cd + 0, fun x => xuR E x ^ xuR k x * lpd x,
        fun x => xuR E x * xuR k x + Td x, ?_, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le (xu_t0_E.pos.trans_le hcE)
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hcdd
      · split_ifs with h0
        · rw [xuG_zero]; exact zero_le
        · have hle : E ^ k * cd + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _
          rw [hGp cd 0 h0 hcdE hk0 hle, xuG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((xuQ_le cd).trans hgcd)
      · have hB := hBE x hx hx1 hg
        obtain ⟨e1, e2, e3, e4⟩ := hdd x hx hx1 (hgd x hg)
        beta_reduce
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hRc0, e1, mul_add, gu_pow_eq hB, ← opow_add]
        · obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gu_pow_eq hB, ← opow_add]⟩
        · exact (lt_of_lt_of_le (mul_pos hB.pos (hKpos x hx hx1 hg)) le_self_add).ne'
        · split_ifs with h0
          · rw [h0, xuR_zero] at e4
            rw [nonpos_iff_eq_zero.1 e4, mul_zero, xuR_zero]
          · rw [hRp cd 0 x h0 hcdE hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _), xuR_zero,
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
    have hgr : ∀ x, xuG c < x → xuG r < x := fun x h => (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt (hgc ▸ h))
    have hrB : r < gcG 1 := hrc.trans hc
    obtain ⟨cr, lpr, Tr, hcrr, hgcr, hdr, hexr⟩ := IH r hrc hrl hrB
    have hcrk : cr < E ^ k := hcrr.trans hr
    have hle : E ^ k * d + cr ≤ c := by rw [← hdec]; exact add_le_add le_rfl hcrr.le
    refine ⟨E ^ k * d + cr, fun x => xuR E x ^ xuR k x * xuR d x + lpr x, Tr, ?_, ?_,
      fun x hx hx1 hg => ?_, fun σ ρ hB hg => hexr σ ρ hB (hgr σ hg)⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hcrr
    · rw [hGp d cr hd0 hdE hcrk hle, hgc]; exact max_le_max le_rfl (max_le_max le_rfl hgcr)
    · have hB := hBE x hx hx1 hg
      obtain ⟨e1, e2, e3, e4⟩ := hdr x hx hx1 (hgr x hg)
      beta_reduce
      have hωx := omega0_lt_inE hx
      obtain ⟨-, g0k, -, g0r⟩ := hgx x hωx hg
      have hgE : xuG E < x := xu_E_g hcE hc hg
      -- the logend of `r(x)` lies below `B·K`
      have hTle : Tr x ≤ xuR E x * xuR k x := by
        have hb := xu_bound_of hx hx1 (fun j hj => (xu_mono_top hx hx1 j hj).1)
          (fun j hj => (xu_mono_top hx hx1 j hj).2) hEcE hEt hEB hgE (xu_mono_top hx hx1 E hEB).1
          r hrB hrB g0r (hrc.trans hcN') k hk (hkc.trans hc) (hkc.trans hc) g0k hr
        rw [gu_pow_eq hB] at hb
        have h1 : ω ^ Tr x ≤ xuR r x := by rw [e1]; exact le_add_self
        exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
      refine ⟨by rw [hRc, e1, add_assoc], Ge.dvd_add' (gu_dvd hB hTle) e2, e3, ?_⟩
      rw [hRp d cr x hd0 hdE hcrk hle]
      exact add_le_add le_rfl e4

end Googology.Trans.PoR.InaccPsi.R2.Yh
