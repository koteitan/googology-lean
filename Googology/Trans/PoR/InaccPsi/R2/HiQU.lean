import Googology.Trans.PoR.InaccPsi.R2.HiQL

/-!
# HiQU: THE UNION OVER ALL LEVELS OVER A GATED BASE `Q`: THE NEXT `Ω₁`-POINT `hdNx Ω₁ Q`, READ `Ω₁ ↦ x`

The gated version of `Hg.hgQU`: for a gated base `B : Hi.HiQB` with a start `U` at `Q`, the systems `Hi.hiQL ν`,
`ν < Ω₁`, form a union (`hiQU`, an `Hg.HgVD`) with the bound `hdNx Ω₁ Q` (the least point of `range φ(Ω₁, ·)` above
`Q`), the base gate `γ`, the base reading `hdNx x (P x)` above `γ` (the level `Ω₁` read as the base `x`), and the
bound field `evZ(hdNx x (P x))` above `γ`, `Z_o(x)` below.  SMALL holds (`hiQ_small`, by one induction on the level
with `Hg.hgQ_highN`: the codes past the start of the level `ω + ν` have a gate `≥ max(γ, ω + ν)`).  The union extends
its start, reads `Q` as `P(x)` (`hiQU_RQ`, `hiQU_gQ`), and has the HIGH property (`hiQU_high`).

* `hiQ_small`, `hiQN`, `hiQZ`, `hiQU` (**THE UNION OVER ALL LEVELS OVER A GATED `Q`**), `hiQU_B`, `hiQU_γ`, `hiQU_b`,
  `hiQU_Z`, `hiQU_R`, `hiQU_g`, `hiQU_high`, `hiQU_ext`, `hiQU_RQ`, `hiQU_gQ`, `hiQU_loc` (gate `γ < K`).

No new axiom.  New definitions: `hiQN`, `hiQZ`, `hiQU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

section Union

variable (B : HiQB) (U : HgVD) (hU : HiQStart B U)

/-- **SMALL OVER `Q`**: a code of `hiQL ν` with gate below an `ε`-number `σ` lies in some `hiQL μ`, `μ < σ` (one
induction on the level: the codes past the start of the level `ω + ν` have a gate `≥ ω + ν`, `hgQ_highN`). -/
theorem hiQ_small : ∀ ν, ν < Om1 → ∀ c, c < (hiQL B U hU ν).B → ∀ σ, InE σ → σ < Om1 → (hiQL B U hU ν).g c < σ →
    ∃ μ, μ < σ ∧ c < (hiQL B U hU μ).B := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν c hc σ hσ hσ1 hg
  by_cases hνσ : ν < σ
  · exact ⟨ν, hνσ, hc⟩
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · exact absurd (by rw [h0]; exact hσ.pos) hνσ
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    by_cases hcμ : c < (hiQL B U hU μ).B
    · have e := ((hiQL_inv B U hU (μ + 1) hν).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hH : ∃ hν' : μ + 1 < Om1, HiQOK B μ (hiQL B U hU μ) := ⟨hν, (hiQL_inv B U hU μ hμ1).1⟩
      set hS := (hiQ_OK_start B hH.choose hH.choose_spec).choose_spec.choose_spec.choose_spec with hhS
      have e : hiQL B U hU (μ + 1) =
          hgfMTU (St := hgfLS (μ + 1)) (fun Q U h => hgfLS_spec hH.choose Q U h) hS := by
        rw [hiQL_succ]; unfold hiQLSucc; rw [dif_pos hH]
      rw [e] at hc hg
      have h := hgQ_highN _ hS hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt ((le_max_right _ _).trans_lt h))
  · have hcoh : HiQCoh B ν (fun ν' _ => hiQL B U hU ν') :=
      ⟨fun ν' h => (hiQL_inv B U hU ν' (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (hiQL_inv B U hU ν₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hiQLCh_start B ν hlim hν (fun ν' _ => hiQL B U hU ν') hcoh
    have e : hiQL B U hU ν = hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS := by
      rw [hiQL_limit B U hU hlim]; unfold hiQLLim; rw [dif_pos ⟨hν, hcoh⟩]
    by_cases hcS : c < hdNx (ω + ν) B.Q
    · rw [hiQL_NxQ B ν hν] at hcS
      obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hgf_lev hν).ne (B.Q_fix _ (hgf_lev hν).2) hcS
      obtain ⟨ν'', hν'', hbν⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hν''1 : ν'' < Om1 := hν''.trans hν
      have hcν : c < (hiQL B U hU ν'').B := by
        rw [(hiQL_inv B U hU ν'' hν''1).1.1]; exact hcb.trans_le (hcN_mono hbν _)
      have e2 := ((hiQL_inv B U hU ν hν).2 ν'' hν''.le c 0 hcν).2
      rw [e2] at hg
      exact IH ν'' hν'' hν''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [e] at hc hg
      have h := hgQ_highN _ hS hc (not_lt.1 hcS) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt ((le_max_right _ _).trans_lt h))


/-! ## The union over all levels over `Q` -/

theorem hiQ_Om1_ne : (Om1 : Ordinal.{0}) ≠ 0 := gv_Om1_pos.ne'

/-- **Every `hiQL ν`, `ν < Ω₁`, lies below `hdNx Ω₁ Q`.** -/
theorem hiQB_gt {ν : Ordinal.{0}} (hν : ν < Om1) : (hiQL B U hU ν).B < hdNx Om1 B.Q := by
  rw [(hiQL_inv B U hU ν hν).1.1]; exact hdN_lt_Nx (gv_Om1_lim.add_one_lt (hgf_lev hν).2)

/-- **The bounds `φ(ω+ν+1, Q+1)`, `ν < Ω₁`, are cofinal in `hdNx Ω₁ Q`.** -/
theorem hiQB_cof {c : Ordinal.{0}} (hc : c < hdNx Om1 B.Q) : ∃ ν, ν < Om1 ∧ c < (hiQL B U hU ν).B := by
  obtain ⟨b, hb, hcb⟩ := hgNx_cof hiQ_Om1_ne B.Q_fix hc
  exact ⟨b, hb, by rw [(hiQL_inv B U hU b hb).1.1]; exact hcb.trans_le (hcN_mono le_add_self _)⟩

theorem hiQB_lt1 : hdNx Om1 B.Q < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen Om1 (gcG 1) = gcG 1 := gn_veb_fix hG1 (hg_Om1_lt_G 1)
  have h2 := (isNormal_veblen Om1).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt B.Q_lt1)
  rw [hfix] at h2
  exact (hdNx_min ((lt_add_one _).trans_le (right_le_veblen _ _))).trans_lt h2

theorem hiQB_E : InE (hdNx Om1 B.Q) := hdNx_E hiQ_Om1_ne _

theorem hiQB_lim : IsSuccLimit (hdNx Om1 B.Q) := ev_isSuccLimit_of_inE (hiQB_E B)

/-- The first level containing `c`. -/
noncomputable def hiQN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < Om1 ∧ c < (hiQL B U hU ν).B}

theorem hiQN_spec {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hiQL B U hU ν).B) :
    hiQN B U hU c ≤ ν ∧ hiQN B U hU c < Om1 ∧ c < (hiQL B U hU (hiQN B U hU c)).B := by
  have hne : ({ν | ν < Om1 ∧ c < (hiQL B U hU ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem hiQN_high {c : Ordinal.{0}} (hc : hdNx Om1 B.Q ≤ c) : hiQN B U hU c = 0 := by
  unfold hiQN
  have he : ({ν | ν < Om1 ∧ c < (hiQL B U hU ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hiQB_gt B U hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hiQ_R_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hiQL B U hU ν).B) (x : Ordinal.{0}) :
    (hiQL B U hU (hiQN B U hU c)).R c x = (hiQL B U hU ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hiQN_spec B U hU hν hc
  exact ((hiQL_inv B U hU ν hν).2 _ h1 c x h3).1.symm

theorem hiQ_g_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hiQL B U hU ν).B) :
    (hiQL B U hU (hiQN B U hU c)).g c = (hiQL B U hU ν).g c := by
  obtain ⟨h1, -, h3⟩ := hiQN_spec B U hU hν hc
  exact ((hiQL_inv B U hU ν hν).2 _ h1 c 0 h3).2.symm

theorem hiQ_R_succ (c x : Ordinal.{0}) :
    (hiQL B U hU (hiQN B U hU (c + 1))).R (c + 1) x = (hiQL B U hU (hiQN B U hU c)).R c x + 1 := by
  rcases lt_or_ge c (hdNx Om1 B.Q) with h | h
  · obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU ((hiQB_lim B).add_one_lt h)
    rw [hiQ_R_eq B U hU hn1 hn, hiQ_R_eq B U hU hn1 ((lt_add_one c).trans hn), (hiQL B U hU n).R_succ]
  · rw [hiQN_high B U hU h, hiQN_high B U hU (h.trans (le_self_add (a := c) (b := 1))), (hiQL B U hU 0).R_succ]

theorem hiQ_g_le_succ (c : Ordinal.{0}) :
    (hiQL B U hU (hiQN B U hU c)).g c ≤ (hiQL B U hU (hiQN B U hU (c + 1))).g (c + 1) := by
  rcases lt_or_ge c (hdNx Om1 B.Q) with h | h
  · obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU ((hiQB_lim B).add_one_lt h)
    rw [hiQ_g_eq B U hU hn1 hn, hiQ_g_eq B U hU hn1 ((lt_add_one c).trans hn)]; exact (hiQL B U hU n).g_le_succ c
  · rw [hiQN_high B U hU h, hiQN_high B U hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hiQL B U hU 0).g_le_succ c

/-- **The bound field of every `hiQL ν` lies below `Z_o(x)`.** -/
theorem hiQ_Z_le {ν x : Ordinal.{0}} (hν : ν < Om1) (hx : InE x) (hx1 : x < Om1) : (hiQL B U hU ν).Z x ≤ B.Zo x := by
  rw [(hiQL_inv B U hU ν hν).1.2.2.2.1 x hx hx1]
  split_ifs with h
  · exact (B.evN_lt_Zo hx hx1 (max_lt_iff.1 h).1 (max_lt_iff.1 h).2).le
  · exact le_rfl

/-- **The base reading of `hiQL ν` lies below `hdNx x (P(x))`** (`γ, ν < x`). -/
theorem hiQ_b_lt {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : B.γ < x) (hν : ν < x) :
    (hiQL B U hU ν).b x < hdNx x (B.P x) := by
  rw [(hiQL_inv B U hU ν (hν.trans hx1)).1.2.2.1 x hx hx1 (max_lt hγ (hg_lev_lt hx hx1 hν))]
  exact hdN_lt_Nx ((ev_isSuccLimit_of_inE hx).add_one_lt (hg_lev_lt hx hx1 hν))

/-- **The bound field of `hiQL ν` lies below `hdNx x (P(x))`** (`γ, ν < x`). -/
theorem hiQ_Z_lt {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : B.γ < x) (hν : ν < x) :
    (hiQL B U hU ν).Z x < hdNx x (B.P x) := by
  have hl := hg_lev_lt hx hx1 hν
  rw [(hiQL_inv B U hU ν (hν.trans hx1)).1.2.2.2.1 x hx hx1, if_pos (max_lt hγ hl)]
  exact hb_evZ_lt_fix2 (hdNx_fix (show (2 : Ordinal.{0}) < x from (show (2 : Ordinal.{0}) < ω from
    by exact_mod_cast natCast_lt_omega0 2).trans (omega0_lt_inE hx)) _)
    (hdN_lt_Nx ((ev_isSuccLimit_of_inE hx).add_one_lt hl))

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hiQL μ`, `μ < σ`.** -/
theorem hiQ_small' {c σ : Ordinal.{0}} (hc : c < hdNx Om1 B.Q) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hiQL B U hU (hiQN B U hU c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hiQL B U hU μ).B := by
  obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
  rw [hiQ_g_eq B U hU hn1 hn] at hg
  exact hiQ_small B U hU n hn1 c hn σ hσ hσ1 hg

theorem hiQ_γ_lt {μ x : Ordinal.{0}} (hx : InE x) (hγ : B.γ < x) (hμ : μ < x) (hμ1 : μ < Om1) :
    (hiQL B U hU μ).γ < x :=
  (hiQL_γ B U hU hμ1).trans_lt (max_lt hγ ((inE_indec hx).add_lt (omega0_lt_inE hx) hμ))

/-- The bound field of the union: `evZ(hdNx x (P(x)))` above `γ`, `Z_o(x)` at or below it. -/
noncomputable def hiQZ (x : Ordinal.{0}) : Ordinal.{0} := if B.γ < x then evZ (hdNx x (B.P x)) else B.Zo x

theorem hiQZ_fix (x : Ordinal.{0}) : veblen 1 (hiQZ B x) = hiQZ B x := by
  unfold hiQZ; split_ifs
  · exact epsilon_evZ _
  · exact B.Zo_fix1 x

theorem hiQZ_G1 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hiQZ B x < gq 1 x := by
  unfold hiQZ; split_ifs with h
  · exact gw_evZ_lt1 hx hx1 (B.Pn_lt hx hx1 h)
  · exact B.Zo_G1 x hx hx1

/-- **A code of the union with gate below `x` has its reading below `hdNx x (P(x))`** (`γ < x`). -/
theorem hiQ_R_lt_b {c x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : B.γ < x) (hc : c < hdNx Om1 B.Q)
    (hg : (hiQL B U hU (hiQN B U hU c)).g c < x) : (hiQL B U hU (hiQN B U hU c)).R c x < hdNx x (B.P x) := by
  obtain ⟨μ, hμσ, hcμ⟩ := hiQ_small' B U hU hc hx hx1 hg
  have hμ1 : μ < Om1 := hμσ.trans hx1
  rw [hiQ_R_eq B U hU hμ1 hcμ]; rw [hiQ_g_eq B U hU hμ1 hcμ] at hg
  exact ((hiQL B U hU μ).R_lt_Z x hx hx1 c hcμ hg).trans (hiQ_Z_lt B U hU hx hx1 hγ hμσ)

/-- **THE UNION OVER ALL LEVELS OVER A GATED `Q`**: bound `hdNx Ω₁ Q`, base gate `γ`, base reading `hdNx x (P x)`
(the level `Ω₁` read as `x`), bound field `evZ(hdNx x (P x))` above `γ`, `Z_o(x)` below. -/
noncomputable def hiQU : HgVD where
  B := hdNx Om1 B.Q
  γ := B.γ
  γ_lt := B.γ_lt
  γ_cl := fun Z hZ hZ1 h => B.Qn_cl Z hZ hZ1 h
  γ_G := fun h => absurd h (B.G_lt.trans (hdNx_gt _ _)).ne'
  R := fun c x => (hiQL B U hU (hiQN B U hU c)).R c x
  g := fun c => (hiQL B U hU (hiQN B U hU c)).g c
  b := fun x => hdNx x (B.P x)
  ba := fun x => hdNx x (B.P x)
  ix := hdNx Om1 B.Q
  Z := hiQZ B
  B_E := hiQB_E B
  G_le := B.G_lt.le.trans (hdNx_gt _ _).le
  B_lt1 := hiQB_lt1 B
  B_ix := (hdNx_fix hg_one_lt_Om1 _).symm
  Z_fix := fun x _ _ => hiQZ_fix B x
  Z_G1 := hiQZ_G1 B
  ix_mem := fun S a b ha hb => B.Qn_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    rw [hiQ_g_eq B U hU hn1 hn]; exact (hiQL B U hU n).g_lt c hn
  g_zero := by rw [hiQ_g_eq B U hU gv_Om1_pos (hiQL B U hU 0).B_pos]; exact (hiQL B U hU 0).g_zero
  g_nat := fun k => by
    rw [hiQ_g_eq B U hU gv_Om1_pos ((hiQL B U hU 0).nat_lt_B k)]; exact (hiQL B U hU 0).g_nat k
  g_E := by rw [hiQ_g_eq B U hU gv_Om1_pos (hiQL B U hU 0).E_lt_B]; exact (hiQL B U hU 0).g_E
  g_lowE := fun c hc => by
    rw [hiQ_g_eq B U hU gv_Om1_pos (hc.trans (hiQL B U hU 0).E_lt_B)]; exact (hiQL B U hU 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU h
    rw [hiQ_g_eq B U hU hn1 hn]; exact (hiQL B U hU n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hxy
    have hx : x < (hiQL B U hU n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hiQL B U hU n).B := lt_of_le_of_lt le_add_self hn
    show (hiQL B U hU (hiQN B U hU (x + y))).g (x + y) < Z
    rw [hiQ_g_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hx] at hgx; rw [hiQ_g_eq B U hU hn1 hy] at hgy
    exact (hiQL B U hU n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hy
    have hy' : y < (hiQL B U hU n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hiQL B U hU (hiQN B U hU (ω ^ y))).g (ω ^ y) < Z
    rw [hiQ_g_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hy'] at hg
    exact (hiQL B U hU n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hcB
    show (hiQL B U hU (hiQN B U hU c)).g c < Z
    rw [hiQ_g_eq B U hU hn1 hn]
    exact (hiQL B U hU n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hiQB_gt B U hU hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    have hc' : c < (hiQL B U hU n).B := (lt_add_one c).trans hn
    show (hiQL B U hU (hiQN B U hU (c + 1))).g (c + 1) < Z
    rw [hiQ_g_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hc'] at hg
    exact (hiQL B U hU n).g_succ Z hZ c hn hg
  g_le_succ := hiQ_g_le_succ B U hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    rw [hiQ_g_eq B U hU hn1 hn] at hg
    exact (hiQL B U hU n).mem S a b ha c hn hg
  R_zero := fun x => by rw [hiQ_R_eq B U hU gv_Om1_pos (hiQL B U hU 0).B_pos]; exact (hiQL B U hU 0).R_zero x
  R_nat := fun k x => by
    rw [hiQ_R_eq B U hU gv_Om1_pos ((hiQL B U hU 0).nat_lt_B k)]; exact (hiQL B U hU 0).R_nat k x
  R_E := fun x => by rw [hiQ_R_eq B U hU gv_Om1_pos (hiQL B U hU 0).E_lt_B]; exact (hiQL B U hU 0).R_E x
  R_succ := hiQ_R_succ B U hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    show 0 < (hiQL B U hU (hiQN B U hU c)).R c x
    rw [hiQ_R_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hn] at hg
    exact (hiQL B U hU n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    show ω ≤ (hiQL B U hU (hiQN B U hU c)).R c x
    rw [hiQ_R_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hn] at hg
    exact (hiQL B U hU n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγ c hc hg => hiQ_R_lt_b B U hU hx hx1 hγ hc hg
  R_lt_Z := fun x hx hx1 c hc hg => by
    show (hiQL B U hU (hiQN B U hU c)).R c x < hiQZ B x
    by_cases hγ : B.γ < x
    · unfold hiQZ; rw [if_pos hγ]
      exact (hiQ_R_lt_b B U hU hx hx1 hγ hc hg).trans (lt_evZ _)
    · obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
      unfold hiQZ; rw [if_neg hγ]
      rw [hiQ_R_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hn] at hg
      exact ((hiQL B U hU n).R_lt_Z x hx hx1 c hn hg).trans_le (hiQ_Z_le B U hU hn1 hx hx1)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    have hd : d < (hiQL B U hU n).B := hdc.trans hn
    show (hiQL B U hU (hiQN B U hU d)).R d x < (hiQL B U hU (hiQN B U hU c)).R c x
    rw [hiQ_R_eq B U hU hn1 hn, hiQ_R_eq B U hU hn1 hd]; rw [hiQ_g_eq B U hU hn1 hn] at hgc
    rw [hiQ_g_eq B U hU hn1 hd] at hgd
    exact (hiQL B U hU n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    rw [hiQ_R_eq B U hU hn1 hn] at hν; rw [hiQ_g_eq B U hU hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hiQL B U hU n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hiQL B U hU n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hiQL B U hU (hiQN B U hU d)).g d < x; rw [hiQ_g_eq B U hU hn1 hd]; exact hgd,
      by show ν ≤ (hiQL B U hU (hiQN B U hU d)).R d x; rw [hiQ_R_eq B U hU hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨b, hb, hνb⟩ := hgNx_cof hx.pos.ne' (fun b hb => B.P_fixL hx hx1 hγ hb) hν
    have hb1 : b < Om1 := hb.trans hx1
    have hνb' : ν < (hiQL B U hU b).b x := by
      rw [(hiQL_inv B U hU b hb1).1.2.2.1 x hx hx1 (max_lt hγ (hg_lev_lt hx hx1 hb))]
      exact hνb.trans_le (hcN_mono le_add_self _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hiQL B U hU b).b_cof x hx hx1 (hiQ_γ_lt B U hU hx hγ hb hb1) ν hνb'
    exact ⟨d, hd.trans (hiQB_gt B U hU hb1),
      by show (hiQL B U hU (hiQN B U hU d)).g d < x; rw [hiQ_g_eq B U hU hb1 hd]; exact hgd,
      by show ν < (hiQL B U hU (hiQN B U hU d)).R d x; rw [hiQ_R_eq B U hU hb1 hd]; exact hνd⟩
  b_E := fun x hx _ _ => hdNx_E hx.pos.ne' _
  x_lt_b := fun x hx hx1 hγ => (B.P_gtL hx hx1 hγ).trans (hdNx_gt _ _)
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1
    (hdNx_fix (one_lt_omega0.trans (omega0_lt_inE hx)) _) ((B.P_gtL hx hx1 hγ).trans (hdNx_gt _ _))
    (B.Pn_lt hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => B.Pn_lt hx hx1 hγ
  b_Z := fun x _ _ hγ => by
    show _ < hiQZ B x
    unfold hiQZ; rw [if_pos hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun σ ρ hB hγ => B.Pn_pi hB hγ
  ba_pi := fun σ ρ hB hγ => B.Pn_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    show (hiQL B U hU (hiQN B U hU c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((hiQL B U hU (hiQN B U hU c)).R c ρ) = (hiQL B U hU (hiQN B U hU c)).R c σ
    rw [hiQ_R_eq B U hU hn1 hn, hiQ_R_eq B U hU hn1 hn]; rw [hiQ_g_eq B U hU hn1 hn] at hg
    exact (hiQL B U hU n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hiQ_small' B U hU hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hiQL B U hU (hiQN B U hU d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hiQL B U hU (hiQN B U hU d)).R d ρ) = ω ^ P' * (hiQL B U hU (hiQN B U hU d)).R d σ
    rw [hiQ_R_eq B U hU hμ1 hdμ, hiQ_R_eq B U hU hμ1 hdμ]; rw [hiQ_g_eq B U hU hμ1 hdμ] at hg
    exact (hiQL B U hU μ).dig σ ρ hB (hiQ_γ_lt B U hU hB.1 hγσ hμσ hμ1) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hiQ_b_lt B U hU hB.2.1 hB.2.2.2 (hγσ.trans hB.2.2.1) (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hiQL B U hU n).ld c hl hn
    have hcpn : cp < (hiQL B U hU n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hiQL B U hU (hiQN B U hU cp)).g cp ≤ (hiQL B U hU (hiQN B U hU c)).g c
      rw [hiQ_g_eq B U hU hn1 hn, hiQ_g_eq B U hU hn1 hcpn]; exact hgcp
    · have hg' : (hiQL B U hU n).g c < x := by rw [← hiQ_g_eq B U hU hn1 hn]; exact hg
      show (hiQL B U hU (hiQN B U hU c)).R c x = _ ∧ _
      rw [hiQ_R_eq B U hU hn1 hn, hiQ_R_eq B U hU hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hiQ_g_eq B U hU hn1 hn]; exact hg

theorem hiQU_B : (hiQU B U hU).B = hdNx Om1 B.Q := rfl

theorem hiQU_γ : (hiQU B U hU).γ = B.γ := rfl

theorem hiQU_b (x : Ordinal.{0}) : (hiQU B U hU).b x = hdNx x (B.P x) := rfl

theorem hiQU_Z (x : Ordinal.{0}) : (hiQU B U hU).Z x = if B.γ < x then evZ (hdNx x (B.P x)) else B.Zo x := rfl

theorem hiQU_ix : (hiQU B U hU).ix = hdNx Om1 B.Q := rfl

/-- **The union extends every `hiQL ν`, `ν < Ω₁`** (readings). -/
theorem hiQU_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hiQL B U hU ν).B) (x : Ordinal.{0}) :
    (hiQU B U hU).R c x = (hiQL B U hU ν).R c x := hiQ_R_eq B U hU hν hc x

/-- **The union extends every `hiQL ν`, `ν < Ω₁`** (gates). -/
theorem hiQU_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hiQL B U hU ν).B) :
    (hiQU B U hU).g c = (hiQL B U hU ν).g c := hiQ_g_eq B U hU hν hc

/-- **HIGH for the union**: a code `c ∈ [Q, hdNx Ω₁ Q)` with gate below an `ε`-number `σ` forces `γ < σ`. -/
theorem hiQU_high {c σ : Ordinal.{0}} (hFc : B.Q ≤ c) (hc : c < hdNx Om1 B.Q) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hiQU B U hU).g c < σ) : B.γ < σ := by
  obtain ⟨n, hn1, hn⟩ := hiQB_cof B U hU hc
  rw [hiQU_g B U hU hn1 hn] at hg
  exact (hiQL_inv B U hU n hn1).1.2.2.2.2 c σ hFc hn hσ hσ1 hg

/-- **The union over all levels over `Q` extends its start `U`.** -/
theorem hiQU_ext {c : Ordinal.{0}} (hc : c < U.B) :
    (∀ x, (hiQU B U hU).R c x = U.R c x) ∧ (hiQU B U hU).g c = U.g c := by
  have hUB : U.B = B.Q := hg_B_of_start hU
  have hQW : c < (hiQW B U hU).B := by
    rw [(hiQW_spec B U hU).B]; show c < hcS B.Q; rw [← hUB]; exact hc.trans (hcS_gt _)
  have hQL : c < (hiQL B U hU 0).B := by
    rw [hiQL_zero, hiQT_B]; exact hQW.trans_le (by rw [(hiQW_spec B U hU).B]; exact (hdS_lt_Nw (hcNw_gt _)).le)
  refine ⟨fun x => ?_, ?_⟩
  · rw [hiQU_R B U hU gv_Om1_pos hQL, hiQL_zero]
    show (hgdLvTU (hiQW_start B U hU)).R c x = U.R c x
    rw [hgdLvTU_R0 _ hQW x]; exact (hiQW_spec B U hU).extR c x hc
  · rw [hiQU_g B U hU gv_Om1_pos hQL, hiQL_zero]
    show (hgdLvTU (hiQW_start B U hU)).g c = U.g c
    rw [hgdLvTU_g0 _ hQW]; exact (hiQW_spec B U hU).extg c hc

/-- **The reading of the code `Q` in the union is `P(x)`** (`γ < x`), and its gate is below `x` iff `γ` is. -/
theorem hiQU_RQ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : B.γ < x) : (hiQU B U hU).R B.Q x = B.P x := by
  have hUB : U.B = B.Q := hg_B_of_start hU
  have hQW : B.Q < (hiQW B U hU).B := by rw [(hiQW_spec B U hU).B]; exact hcS_gt _
  have hQL : B.Q < (hiQL B U hU 0).B := by
    rw [hiQL_zero, hiQT_B]; exact hQW.trans_le (by rw [(hiQW_spec B U hU).B]; exact (hdS_lt_Nw (hcNw_gt _)).le)
  rw [hiQU_R B U hU gv_Om1_pos hQL x, hiQL_zero]
  show (hgdLvTU (hiQW_start B U hU)).R B.Q x = B.P x
  rw [hgdLvTU_R0 _ hQW x]; exact (hiQW_spec B U hU).RF x hx hx1 hγ

theorem hiQU_gQ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (hiQU B U hU).g B.Q < x ↔ B.γ < x := by
  have hQW : B.Q < (hiQW B U hU).B := by rw [(hiQW_spec B U hU).B]; exact hcS_gt _
  have hQL : B.Q < (hiQL B U hU 0).B := by
    rw [hiQL_zero, hiQT_B]; exact hQW.trans_le (by rw [(hiQW_spec B U hU).B]; exact (hdS_lt_Nw (hcNw_gt _)).le)
  rw [hiQU_g B U hU gv_Om1_pos hQL, hiQL_zero]
  show (hgdLvTU (hiQW_start B U hU)).g B.Q < x ↔ B.γ < x
  rw [hgdLvTU_g0 _ hQW]; exact (hiQW_spec B U hU).gF x hx hx1

include U hU in
/-- **`hdNx Ω₁ Q` IS LOCATED** when `γ < K`: `Λ⁺ = ι(Γ(hdNx Ω₁ Q)·ω)`, `P(…) < L(0)`. -/
theorem hiQU_loc (S : InaccSeq.{0}) (hK : B.γ < Td.tdK S) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hdNx Om1 B.Q) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hdNx Om1 B.Q) * ω) ∧ Pv S (gcG (hdNx Om1 B.Q) * ω) < Nc.ncL S 0 :=
  hgV_locD (hiQU B U hU) S hK

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hi
