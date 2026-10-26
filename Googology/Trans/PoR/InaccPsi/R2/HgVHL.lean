import Googology.Trans.PoR.InaccPsi.R2.HgVHX

/-!
# HgVHL: TEXTUAL COPY OF `Hc.HcVHL` FOR `Hg.HgVD` (readings below `Γ_{x+2}`)

The declarations of `Hc.HcVHL` with `Hc.HcVD` (bound field `Z(x) ≤ B_x(x)`) replaced by `Hg.HgVD` (bound
field `Z(x) < Γ_{x+2}`); the proofs are unchanged except where the bound enters (`HgVD.R_lt_gq`, the field
`Z_G1`, Lemma IMG in `HgVD.toLD` through `He.he_pkg_G1`).

No new axiom.  New definitions: the copies of the definitions of `Hc.HcVHL` (namespace `HgVD`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace HgVD

variable (D : HgVD)

theorem hdvd {x e k q : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : D.γ < x) (he : e ≤ D.b x * k) :
    ω ^ e ∣ D.b x ^ k * q := by
  rw [D.bpow_eq hx hx1 hγx]
  exact dvd_trans (opow_dvd_opow ω he) (dvd_mul_right _ _)

/-- **The last term of every limit code `c < ε_{B+1}`** with Lemma EXACT for its logend. -/
theorem hld : ∀ c, IsSuccLimit c → c < D.NB → ∃ (cp : Ordinal.{0}) (lp T : Ordinal.{0} → Ordinal.{0}),
    cp < c ∧ D.hG cp ≤ D.hG c ∧
    (∀ x, InE x → x < Om1 → D.hG c < x → D.γ < x →
      D.hR c x = lp x + ω ^ T x ∧ ω ^ T x ∣ lp x ∧ T x ≠ 0 ∧ lp x ≤ D.hR cp x) ∧
    ∀ σ ρ, Bases σ ρ → D.hG c < σ → D.γ < σ → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hc
  rcases lt_or_ge c D.B with hcB | hcE
  · obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hcB
    refine ⟨cp, lp, T, hcp, by rw [D.hG_low hcB, D.hG_low (hcp.trans hcB)]; exact hgcp, fun x hx hx1 hg _ => ?_,
      fun σ ρ hB hg _ => hex σ ρ hB (by rw [← D.hG_low hcB]; exact hg)⟩
    rw [D.hG_low hcB] at hg
    rw [D.hR_low hcB, D.hR_low (hcp.trans hcB)]
    exact hdec x hx hx1 hg
  obtain ⟨hk, hd0, hdE, hr, hdec, hkc, hrc⟩ := D.parts hcE hc
  have hkB : log D.B c < D.NB := hkc.trans hc
  set k := log D.B c with hkdef
  set d := c / D.B ^ k with hddef
  set r := c % D.B ^ k with hrdef
  have hgc : D.hG c = max (max (D.hQ k) (D.Q d)) (D.hG r) := D.hG_dec hcE hc
  have hRc : ∀ x, D.hR c x = D.b x ^ D.hR k x * D.R d x + D.hR r x := fun x => D.hR_dec hcE hc x
  have hcnfB : ∀ b t, b < D.B → t < D.B ^ k → D.B ^ k * b + t < D.NB := by
    intro b t hbE ht
    have hk1B : k + 1 < D.NB := D.NB_lim.add_one_lt hkB
    calc D.B ^ k * b + t < D.B ^ k * b + D.B ^ k := (add_lt_add_iff_left _).2 ht
      _ = D.B ^ k * (b + 1) := by rw [mul_add_one]
      _ ≤ D.B ^ k * D.B := mul_le_mul_left' (Order.add_one_le_of_lt hbE) _
      _ = D.B ^ (k + 1) := by rw [opow_add, opow_one]
      _ < D.NB := D.NB_gt_pow hk1B
  have hRp : ∀ b t x, b ≠ 0 → b < D.B → t < D.B ^ k →
      D.hR (D.B ^ k * b + t) x = D.b x ^ D.hR k x * D.R b x + D.hR t x :=
    fun b t x hb hbE ht => D.hR_cnf hk hb hbE ht (hcnfB b t hbE ht) x
  have hGp : ∀ b t, b ≠ 0 → b < D.B → t < D.B ^ k →
      D.hG (D.B ^ k * b + t) = max (max (D.hQ k) (D.Q b)) (D.hG t) :=
    fun b t hb hbE ht => D.hG_cnf hk hb hbE ht (hcnfB b t hbE ht)
  have hk0 : (0 : Ordinal.{0}) < D.B ^ k := opow_pos _ D.B_pos
  have hgkx : ∀ σ, InE σ → D.hG c < σ → D.hG k < σ := fun σ hσ h =>
    (D.parts_g (omega0_lt_inE hσ) hcE hc h).1
  have hKpos : ∀ x, InE x → x < Om1 → D.γ < x → D.hG c < x → 0 < D.hR k x := fun x hx hx1 hγx hg =>
    D.hR_pos hx hx1 hγx hk hkB (hgkx x hx hg)
  have hbpos : ∀ x, InE x → x < Om1 → D.γ < x → 0 < D.b x := fun x hx hx1 hγx => (D.b_E x hx hx1 hγx).pos
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = B^k·d`
    have hRc0 : ∀ x, D.hR c x = D.b x ^ D.hR k x * D.R d x := fun x => by
      rw [hRc, hr0, D.hR_zero, add_zero]
    have hgc0 : D.hG c = max (D.hQ k) (D.Q d) := by rw [hgc, hr0, D.hG_zero, max_eq_left zero_le]
    have hcd : c = D.B ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`: the logend is `b(x)·k(x)`
      rw [succ_eq_add_one] at hsucc
      have hd'E : d' < D.B := (lt_add_one d').trans (by rw [hsucc]; exact hdE)
      have hcpc : D.B ^ k * d' + 0 < c := by
        rw [add_zero, hcd, ← hsucc]; exact (mul_lt_mul_iff_right₀ hk0).2 (lt_add_one d')
      refine ⟨if d' = 0 then 0 else D.B ^ k * d' + 0, fun x => D.b x ^ D.hR k x * D.R d' x,
        fun x => D.b x * D.hR k x, ?_, ?_, fun x hx hx1 hgx hγx => ?_, fun σ ρ hB hg hγ => ?_⟩
      · split_ifs with h0
        · exact (lt_of_le_of_lt zero_le hcpc)
        · exact hcpc
      · split_ifs with h0
        · rw [D.hG_zero]; exact zero_le
        · rw [hGp d' 0 h0 hd'E hk0, D.hG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          exact max_le_max le_rfl (D.Q_le_succ d')
      · beta_reduce
        refine ⟨by rw [hRc0, ← hsucc, D.R_succ, mul_add_one, D.bpow_eq hx hx1 hγx],
          D.hdvd hx hx1 hγx le_rfl, (mul_pos (hbpos x hx hx1 hγx) (hKpos x hx hx1 hγx hgx)).ne', ?_⟩
        split_ifs with h0
        · rw [h0, D.R_zero, mul_zero]; exact zero_le
        · rw [hRp d' 0 x h0 hd'E hk0, D.hR_zero, add_zero]
      · exact D.mulB_pi hB hγ hk hkB (hgkx σ hB.1 hg)
    · -- `d` a limit: the logend is `b(x)·k(x) + T_d(x)`
      obtain ⟨cpd, lpd, Td, hcpd, hgcpd, hdecd, hexd⟩ := D.ld d hdl hdE
      have hdω : ω ≤ d := Ordinal.le_of_dvd hd0 ((isSuccLimit_iff_omega0_dvd.1 hdl).2)
      have hQd : D.Q d = D.g d := D.Q_inf hdω
      have hgd : ∀ x, D.hG c < x → D.g d < x := fun x h => by
        rw [hgc0, hQd] at h; exact (le_max_right _ _).trans_lt h
      have hcpdE : cpd < D.B := hcpd.trans hdE
      have hcpc : D.B ^ k * cpd + 0 < c := by
        rw [add_zero, hcd]; exact (mul_lt_mul_iff_right₀ hk0).2 hcpd
      refine ⟨if cpd = 0 then 0 else D.B ^ k * cpd + 0, fun x => D.b x ^ D.hR k x * lpd x,
        fun x => D.b x * D.hR k x + Td x, ?_, ?_, fun x hx hx1 hgx hγx => ?_, fun σ ρ hB hg hγ => ?_⟩
      · split_ifs with h0
        · exact (lt_of_le_of_lt zero_le hcpc)
        · exact hcpc
      · split_ifs with h0
        · rw [D.hG_zero]; exact zero_le
        · rw [hGp cpd 0 h0 hcpdE hk0, D.hG_zero, max_eq_left zero_le, hgc0, hQd]
          exact max_le_max le_rfl ((D.Q_le cpd).trans hgcpd)
      · obtain ⟨e1, e2, -, e4⟩ := hdecd x hx hx1 (hgd x hgx)
        beta_reduce
        refine ⟨by rw [hRc0, e1, mul_add, D.bpow_eq hx hx1 hγx, ← opow_add], ?_,
          (add_pos_of_pos_of_nonneg (mul_pos (hbpos x hx hx1 hγx) (hKpos x hx hx1 hγx hgx)) zero_le).ne', ?_⟩
        · obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, D.bpow_eq hx hx1 hγx, ← opow_add]⟩
        · split_ifs with h0
          · rw [h0, D.R_zero] at e4
            rw [le_zero_iff.1 e4, mul_zero]; exact zero_le
          · rw [hRp cpd 0 x h0 hcpdE hk0, D.hR_zero, add_zero]
            exact mul_le_mul_left' e4 _
      · obtain ⟨h1, h2⟩ := D.mulB_pi hB hγ hk hkB (hgkx σ hB.1 hg)
        obtain ⟨h3, h4⟩ := hexd σ ρ hB (hgd σ hg)
        obtain ⟨h5, h6⟩ := pi_add hB h1 h3
        exact ⟨h5, by rw [h6, h2, h4]⟩
  · -- `r ≠ 0`: `r` a limit
    have hrl : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hsucc⟩ | hrl
      · exact absurd h0 hr0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (D.B ^ k * d + r') := by rw [← hdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hrl
    have hgr : ∀ x, D.hG c < x → D.hG r < x := fun x h => (le_max_right _ _).trans_lt (hgc ▸ h)
    have hrB : r < D.NB := hrc.trans hc
    obtain ⟨cpr, lpr, Tr, hcpr, hgcpr, hdecr, hexr⟩ := IH r hrc hrl hrB
    have hcprk : cpr < D.B ^ k := hcpr.trans hr
    refine ⟨D.B ^ k * d + cpr, fun x => D.b x ^ D.hR k x * D.R d x + lpr x, Tr, ?_, ?_,
      fun x hx hx1 hgx hγx => ?_, fun σ ρ hB hg hγ => hexr σ ρ hB (hgr σ hg) hγ⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hcpr
    · rw [hGp d cpr hd0 hdE hcprk, hgc]; exact max_le_max le_rfl hgcpr
    · obtain ⟨e1, e2, e3, e4⟩ := hdecr x hx hx1 (hgr x hgx) hγx
      beta_reduce
      -- the logend of `r(x)` lies below `b(x)·k(x)`
      have hb := D.hR_bound hx hx1 hγx hrB (hgr x hgx) hk hkB (hgkx x hx hgx) hr
      rw [D.bpow_eq hx hx1 hγx] at hb
      have hTle : Tr x ≤ D.b x * D.hR k x := by
        have h1 : ω ^ Tr x ≤ D.hR r x := by rw [e1]; exact le_add_self
        exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
      refine ⟨by rw [hRc, e1, add_assoc], Ge.dvd_add' (D.hdvd hx hx1 hγx hTle) e2, e3, ?_⟩
      rw [hRp d cpr x hd0 hdE hcprk]
      exact add_le_add le_rfl e4

end HgVD

end Googology.Trans.PoR.InaccPsi.R2.Hg
