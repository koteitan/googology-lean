import Googology.Trans.PoR.InaccPsi.R2.GkU7

/-!
# CODES BELOW `ζ_{Ω₁+1}`: the last term of a limit code, with Lemma EXACT for its logend

For every limit code `c < ζ_{Ω₁+1}` the reading splits as `c(x) = l'(x) + ω^{T(x)}` with `ω^{T(x)} ∣ l'(x)`,
`l'(x) ≤ c'(x)` for a code `c' < c` (gate at most that of `c`), and the logend `T` has LEMMA EXACT at every pair of
bases above the gate (`GuLD`).  One induction: `c < ε_{Ω₁+1}` by `rdc_lim_facts` (the term `tlg`), `c = ε_{Ω₁+1}`
directly, and `c = E^k·d + r`: the rest `r` (a limit), or `d = d'+1` (logend `ε_{x+n(x)}·k(x)`, `gu_BK_pi`), or `d`
a limit (logend `ε_{x+n(x)}·k(x) + T_d(x)`).  Lemma IMG for the logend is then `gkPkg_of_ex` (`R2.GkPkg`).

* `GuLD`, `gu_ld_low`, `gu_ld_E`, `gu_ld` (**the induction**), `gu_GiLD` (**the field `ld` of a reading system**).

No new axiom.  New definition: `GuLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **The last term of a limit code `c`** with Lemma EXACT for its logend. -/
def GuLD (c : Ordinal.{0}) : Prop :=
  ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}), cp < c ∧ guG cp ≤ guG c ∧
    (∀ x, InE x → x < Om1 → guG c < x →
      guR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ guR cp x) ∧
    ∀ σ ρ, Bases σ ρ → guG c < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ

/-- A limit code below `ε_{Ω₁+1}` (`rdc_lim_facts`, the term `tlg`). -/
theorem gu_ld_low {c : Ordinal.{0}} (hl : IsSuccLimit c) (hc : c < gfE) : GuLD c := by
  obtain ⟨a', l, d, ha', hga', hgl, hd, -, hF⟩ := rdc_lim_facts hl hc
  have ha'E : a' < gfE := ha'.trans hc
  refine ⟨a', fun x => rdc a' x, fun x => OT.ev (tlg l d) x, ha', by rw [guG_low hc, guG_low ha'E]; exact hga',
    fun x hx _ hg => ?_, fun σ ρ hB hg => ?_⟩
  · rw [guG_low hc] at hg
    obtain ⟨e1, e2, e3, -, -, e6⟩ := hF x hx hg
    beta_reduce
    rw [guR_low hc, guR_low ha'E, ← e3]
    exact ⟨e1, e2, (Gc.gc_lg_pos e6).ne', le_rfl⟩
  · rw [guG_low hc] at hg
    exact pi_ev hB _ (cb_tlg hB.1.pos (hgl.trans_lt hg) (hd.trans_lt hg))

/-- The code `ε_{Ω₁+1}`: `ε_{x+1} = 0 + ω^{ε_{x+1}}`. -/
theorem gu_ld_E : GuLD gfE := by
  refine ⟨0, fun _ => 0, eN, eW_E.pos, by rw [guG_zero]; exact zero_le, fun x _ _ _ => ?_,
    fun σ ρ hB _ => gh_eN_pi hB⟩
  beta_reduce
  rw [guR_E, zero_add, show ω ^ eN x = eN x from eN_E x, guR_zero]
  exact ⟨rfl, dvd_zero _, (eN_E x).pos.ne', le_rfl⟩

/-- `ω^e ∣ B^K·q` when `e ≤ B·K` (`B` an `ε`-number). -/
theorem gu_dvd {B K e q : Ordinal.{0}} (hB : InE B) (he : e ≤ B * K) : ω ^ e ∣ B ^ K * q := by
  rw [gu_pow_eq hB]
  exact dvd_trans (opow_dvd_opow ω he) (dvd_mul_right _ _)

/-- **THE LAST TERM OF EVERY LIMIT CODE below `ζ_{Ω₁+1}`**, with Lemma EXACT for its logend. -/
theorem gu_ld : ∀ c, IsSuccLimit c → c < guB → GuLD c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc
  rcases lt_or_ge c gfE with hcE | hcE
  · exact gu_ld_low hl hcE
  rcases hcE.lt_or_eq with hEc | hEc
  swap
  · rw [← hEc]; exact gu_ld_E
  obtain ⟨hn1, hnc', hcn, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc, hdc⟩ := gu_parts hcE hc
  have hEcE : InE (guE c) := guE_E c
  have hcN' : c < eN (guE c) := by rw [guE, ← evA_add_one]; exact hcn
  have hkN : log (guE c) c < eN (guE c) := hkc.trans hcN'
  set n := guN c with hndef
  set E := guE c with hEdef
  set k := log E c with hkdef
  set d := c / E ^ k with hddef
  set r := c % E ^ k with hrdef
  have hEeq : E = evA Om1 n := rfl
  have hgc : guG c = max (max (guQ n) (guQ k)) (max (guQ d) (guG r)) := guG_dec hcE hc
  have hRc : ∀ x, guR c x = guA x (guR n x) ^ guR k x * guR d x + guR r x := fun x => guR_dec hcE hc x
  have hk0 : (0 : Ordinal.{0}) < E ^ k := opow_pos _ hEcE.pos
  have hcnf : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      E ^ k * b + t < evA Om1 (n + 1) ∧ E ^ k * b + t < guB := fun b t _ _ _ h =>
    ⟨h.trans_lt hcn, h.trans_lt hc⟩
  have hRp : ∀ b t x, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      guR (E ^ k * b + t) x = guA x (guR n x) ^ guR k x * guR b x + guR t x := fun b t x hb hbE ht h =>
    guR_cnf hn1 hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2 x
  have hGp : ∀ b t, b ≠ 0 → b < E → t < E ^ k → E ^ k * b + t ≤ c →
      guG (E ^ k * b + t) = max (max (guQ n) (guQ k)) (max (guQ b) (guG t)) := fun b t hb hbE ht h =>
    guG_cnf hn1 hk hb hbE ht (hcnf b t hb hbE ht h).1 (hcnf b t hb hbE ht h).2
  have hgx : ∀ x, ω < x → guG c < x → guG n < x ∧ guG k < x ∧ guG d < x ∧ guG r < x :=
    fun x hωx h => gu_parts_g hωx hcE hc h
  have hKpos : ∀ x, InE x → 0 < guR k x := fun x hx => guR_pos hx k hk (hkc.trans hc)
  -- the logend `B·K` and its Lemma EXACT
  have hBKex : ∀ σ ρ, Bases σ ρ → guG c < σ →
      guA ρ (guR n ρ) * guR k ρ ∈ TB ρ σ ∧ pi σ ρ (guA ρ (guR n ρ) * guR k ρ) = guA σ (guR n σ) * guR k σ := by
    intro σ ρ hB hg
    obtain ⟨g0n, g0k, -, -⟩ := hgx σ (omega0_lt_inE hB.1) hg
    have hexn := gu_pi hB n hnB g0n
    refine gu_BK_pi hB hn1 hnB g0n hk hkN hexn (fun hω => ?_)
    obtain ⟨-, hB', hg', -⟩ := gu_mulE hn1 hnB k hk hkN
    exact gu_pi hB _ hB' (hg'.trans_lt (max_lt ((guQ_le _).trans_lt g0n) g0k))
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hcd : c = E ^ k * d := by rw [← hdec, hr0, add_zero]
    have hRc0 : ∀ x, guR c x = guA x (guR n x) ^ guR k x * guR d x := fun x => by
      rw [hRc, hr0, guR_zero, add_zero]
    have hgc0 : guG c = max (max (guQ n) (guQ k)) (guQ d) := by rw [hgc, hr0, guG_zero, max_eq_left zero_le]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `B·K`
      rw [succ_eq_add_one] at hsucc
      have hd'd : d' < d := by rw [← hsucc]; exact lt_add_one d'
      have hd'E : d' < E := hd'd.trans hdE
      have hdB : d' + 1 < guB := by rw [hsucc]; exact hdc.trans hc
      refine ⟨if d' = 0 then 0 else E ^ k * d' + 0, fun x => guA x (guR n x) ^ guR k x * guR d' x,
        fun x => guA x (guR n x) * guR k x, ?_, ?_, fun x hx _ hg => ?_, hBKex⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le hEc
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hd'd
      · split_ifs with h0
        · rw [guG_zero]; exact zero_le
        · have hle : E ^ k * d' + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _
          rw [hGp d' 0 h0 hd'E hk0 hle, guG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          refine max_le_max le_rfl ?_
          unfold guQ
          by_cases hω : d' < ω
          · rw [if_pos hω]; exact zero_le
          · rw [if_neg hω, if_neg (fun h => hω ((lt_add_one d').trans h))]
            exact guG_le_succ d' hdB
      · have hB := guA_E x (guR n x)
        beta_reduce
        refine ⟨?_, gu_dvd hB le_rfl, (mul_pos hB.pos (hKpos x hx)).ne', ?_⟩
        · rw [hRc0, ← hsucc, guR_succ d' hdB, mul_add_one, gu_pow_eq hB]
        · split_ifs with h0
          · rw [h0, guR_zero, mul_zero]
          · rw [hRp d' 0 x h0 hd'E hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hd'd.le _), guR_zero,
              add_zero]
    · -- `d` a limit: the logend is `B·K + T_d`
      obtain ⟨cd, lpd, Td, hcdd, hgcd, hdd, hexd⟩ := IH d hdc hdl (hdc.trans hc)
      have hdω : ω ≤ d := omega0_le_of_isSuccLimit hdl
      have hQd : guQ d = guG d := by unfold guQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, guG c < x → guG d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcdE : cd < E := hcdd.trans hdE
      refine ⟨if cd = 0 then 0 else E ^ k * cd + 0, fun x => guA x (guR n x) ^ guR k x * lpd x,
        fun x => guA x (guR n x) * guR k x + Td x, ?_, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => ?_⟩
      · split_ifs with h0
        · exact lt_of_le_of_lt zero_le hEc
        · rw [hcd, add_zero]; exact (mul_lt_mul_iff_right₀ hk0).2 hcdd
      · split_ifs with h0
        · rw [guG_zero]; exact zero_le
        · have hle : E ^ k * cd + 0 ≤ c := by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _
          rw [hGp cd 0 h0 hcdE hk0 hle, guG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((guQ_le cd).trans hgcd)
      · have hB := guA_E x (guR n x)
        obtain ⟨e1, e2, e3, e4⟩ := hdd x hx hx1 (hgd x hg)
        beta_reduce
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hRc0, e1, mul_add, gu_pow_eq hB, ← opow_add]
        · obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gu_pow_eq hB, ← opow_add]⟩
        · exact (lt_of_lt_of_le (mul_pos hB.pos (hKpos x hx)) le_self_add).ne'
        · split_ifs with h0
          · rw [h0, guR_zero] at e4
            rw [nonpos_iff_eq_zero.1 e4, mul_zero, guR_zero]
          · rw [hRp cd 0 x h0 hcdE hk0 (by rw [add_zero, hcd]; exact mul_le_mul_right hcdd.le _), guR_zero,
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
    have hgr : ∀ x, guG c < x → guG r < x := fun x h => (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt (hgc ▸ h))
    have hrB : r < guB := hrc.trans hc
    obtain ⟨cr, lpr, Tr, hcrr, hgcr, hdr, hexr⟩ := IH r hrc hrl hrB
    have hcrk : cr < E ^ k := hcrr.trans hr
    have hle : E ^ k * d + cr ≤ c := by rw [← hdec]; exact add_le_add le_rfl hcrr.le
    refine ⟨E ^ k * d + cr, fun x => guA x (guR n x) ^ guR k x * guR d x + lpr x, Tr, ?_, ?_,
      fun x hx hx1 hg => ?_, fun σ ρ hB hg => hexr σ ρ hB (hgr σ hg)⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hcrr
    · rw [hGp d cr hd0 hdE hcrk hle, hgc]; exact max_le_max le_rfl (max_le_max le_rfl hgcr)
    · have hB := guA_E x (guR n x)
      obtain ⟨e1, e2, e3, e4⟩ := hdr x hx hx1 (hgr x hg)
      beta_reduce
      have hωx := omega0_lt_inE hx
      obtain ⟨g0n, g0k, -, g0r⟩ := hgx x hωx hg
      -- the logend of `r(x)` lies below `B·K`
      have hTle : Tr x ≤ guA x (guR n x) * guR k x := by
        have hb := gu_bound_of hx (fun j hj => (gu_mono_top hx j hj).1) (fun j hj => (gu_mono_top hx j hj).2)
          hn1 hnB hnB g0n r hrB hrB g0r (hrc.trans hcn) k hk (hkc.trans hc) (hkc.trans hc) g0k hr
        rw [gu_pow_eq hB] at hb
        have h1 : ω ^ Tr x ≤ guR r x := by rw [e1]; exact le_add_self
        exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
      refine ⟨by rw [hRc, e1, add_assoc], Ge.dvd_add' (gu_dvd hB hTle) e2, e3, ?_⟩
      rw [hRp d cr x hd0 hdE hcrk hle]
      exact add_le_add le_rfl e4

end Googology.Trans.PoR.InaccPsi.R2.Gk
