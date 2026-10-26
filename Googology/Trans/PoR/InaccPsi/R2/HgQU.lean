import Googology.Trans.PoR.InaccPsi.R2.HgQL

/-!
# HgQU: THE UNION OVER ALL LEVELS OVER AN ABSTRACT BASE `Q`: THE NEXT `Ω₁`-POINT `hdNx Ω₁ Q`, READ `Ω₁ ↦ x`

The copy of `Hg.HgU` for an abstract base `B : Hg.HgQB` with a start `U` at `Q`: the systems `Hg.hgQL ν`, `ν < Ω₁`,
form a union (`hgQU`, an `Hg.HgVD`) with the bound `hdNx Ω₁ Q` (the least point of `range φ(Ω₁, ·)` above `Q`), the
base gate `0`, and the base reading `hdNx x (P x) = Z_o(x)`: the level `Ω₁` is read as the base `x`.  SMALL holds
(`hgQ_small`, by one induction on the level, with `hgQ_highN`), so the union is located with base gate `0 < K`.

* `hgQ_highN`, `hgNx_cof` (**`hdNx l Q` is the supremum of `N_b(Q)`, `b < l`, for every common fixed point `Q`**),
  `hgQ_small` (**SMALL OVER `Q`**), `hgQN`, `hgQU` (**THE UNION OVER ALL LEVELS OVER `Q`**), `hgQU_B`, `hgQU_γ`,
  `hgQU_b`, `hgQU_Z`, `hgQU_R`, `hgQU_g`, `hgQU_loc`, `hgQU_enum`, `hgQU_capV`.

No new axiom.  New definitions: `hgQN`, `hgQU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

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

/-- **The codes past the start `S0` of the offset union of a base `A` have a gate `≥` the reading gate `γN`**
(the copy of `Hg.hg_highN` for `Hg.HgVD`). -/
theorem hgQ_highN {α : Ordinal.{0}} {St : ∀ (Q : HgfQ α) (U : HgVD), HgSStart (hgfQPB Q) U → HgVD}
    (hSt : ∀ Q U h, HgfQSpec Q U (St Q U h)) {A : HgfB α} {S0 : HgVD} (hS : HgfMStart A S0)
    {c σ : Ordinal.{0}} (hc : c < hcN α A.F) (hBc : S0.B ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hgfMTU hSt hS).g c < σ) : A.γN < σ := by
  obtain ⟨n, hn1, hn⟩ := hgfMT_cof hSt hS hc
  obtain ⟨-, hN1, hcNc⟩ := hgfMTN_spec hn1 hn
  have hgN : (hgfMTU hSt hS).g c = (hgfMU St A S0 (hgfMTN St A S0 c)).g c := rfl
  have I := hgfM_inv hSt hS _ hN1
  rcases zero_or_succ_or_isSuccLimit (hgfMTN St A S0 c) with h0 | ⟨m, hm⟩ | hlim
  · rw [h0, hgfMU_zero] at hcNc
    exact absurd hBc (not_le.2 hcNc)
  · have hm' : hgfMTN St A S0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hgfMTN St A S0 c := by rw [hm']; exact lt_add_one m
    have hml : m < hcN α A.F := hmN.trans hN1
    have hBc' : (hgfMU St A S0 m).B ≤ c := not_lt.1 (hgfMTN_min hmN hml)
    rw [hgN, hm'] at hg
    rw [hm'] at hcNc I hN1
    have hγ := I.high m (lt_add_one _) c σ hBc' hcNc hσ hσ1 hg
    exact (max_lt_iff.1 ((hgfMU_γ_iff hSt hS hN1 hσ hσ1).1 hγ)).1
  · exfalso
    rw [hgfMU_B hSt hS hN1] at hcNc
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen α).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcNc
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < hcN α A.F := hf.trans hN1
    refine hgfMTN_min hf hfl ?_
    rw [hgfMU_B hSt hS hfl]; exact hct.trans_le ((isNormal_veblen α).monotone htd)

/-- **`hdNx l Q` is the supremum of `N_b(Q)`, `b < l`**, for a common fixed point `Q` of every `φ(b, ·)`, `b < l`. -/
theorem hgNx_cof {l Q : Ordinal.{0}} (hl0 : l ≠ 0) (hQ : ∀ b, b < l → veblen b Q = Q) {c : Ordinal.{0}}
    (hc : c < hdNx l Q) : ∃ b, b < l ∧ c < hcN b Q := by
  obtain ⟨i, hi⟩ : Q ∈ range (veblen l) := (mem_range_veblen hl0).2 hQ
  rw [← hi, hdNx_veb] at hc
  rw [veblen_of_ne_zero hl0] at hc hi
  rw [derivFamily_add_one, hi] at hc
  obtain ⟨L, hL⟩ := lt_nfpFamily_iff.1 hc
  have key : ∀ L : List (Iio l), ∃ b, b < l ∧
      List.foldr (fun x : Iio l => veblen x.1) (Q + 1) L < hcN b Q := by
    intro L
    induction L with
    | nil =>
      exact ⟨0, pos_iff_ne_zero.2 hl0,
        (ev_isSuccLimit_of_inE (hcN_E 0 Q)).add_one_lt (hcN_gt 0 Q)⟩
    | cons i L ih =>
      obtain ⟨b, hb, hbL⟩ := ih
      refine ⟨max b i.1, max_lt hb i.2, ?_⟩
      show veblen i.1 (List.foldr (fun x : Iio l => veblen x.1) (Q + 1) L) < hcN (max b i.1) Q
      calc veblen i.1 (List.foldr (fun x : Iio l => veblen x.1) (Q + 1) L)
          < veblen i.1 (hcN (max b i.1) Q) :=
            (isNormal_veblen i.1).strictMono (hbL.trans_le (hcN_mono (le_max_left _ _) Q))
        _ = hcN (max b i.1) Q := hc_fix_down (le_max_right _ _) (hcN_fix _ Q)
  obtain ⟨b, hb, hbL⟩ := key L
  exact ⟨b, hb, hL.trans hbL⟩

/-! ## SMALL for the level recursion over `Q` -/

section Union

variable (B : HgQB) (U : HgVD) (hU : HgQStart B U)

/-- **SMALL OVER `Q`**: a code of `hgQL ν` with gate below an `ε`-number `σ` lies in some `hgQL μ`, `μ < σ` (one
induction on the level: the codes past the start of the level `ω + ν` have a gate `≥ ω + ν`, `hgQ_highN`). -/
theorem hgQ_small : ∀ ν, ν < Om1 → ∀ c, c < (hgQL B U hU ν).B → ∀ σ, InE σ → σ < Om1 → (hgQL B U hU ν).g c < σ →
    ∃ μ, μ < σ ∧ c < (hgQL B U hU μ).B := by
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
    by_cases hcμ : c < (hgQL B U hU μ).B
    · have e := ((hgQL_inv B U hU (μ + 1) hν).2 μ (le_add_right le_rfl) c 0 hcμ).2
      rw [e] at hg
      exact IH μ (lt_add_one μ) hμ1 c hcμ σ hσ hσ1 hg
    · exfalso
      have hH : ∃ hν' : μ + 1 < Om1, HgQOK B μ (hgQL B U hU μ) := ⟨hν, (hgQL_inv B U hU μ hμ1).1⟩
      set hS := (hgQ_OK_start B hH.choose hH.choose_spec).choose_spec.choose_spec with hhS
      have e : hgQL B U hU (μ + 1) =
          hgfMTU (St := hgfLS (μ + 1)) (fun Q U h => hgfLS_spec hH.choose Q U h) hS := by
        rw [hgQL_succ]; unfold hgQLSucc; rw [dif_pos hH]
      rw [e] at hc hg
      have h := hgQ_highN _ hS hc (not_lt.1 hcμ) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt h)
  · have hcoh : HgQCoh B ν (fun ν' _ => hgQL B U hU ν') :=
      ⟨fun ν' h => (hgQL_inv B U hU ν' (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 c x hc =>
        (hgQL_inv B U hU ν₂ (h₂.trans hν)).2 ν₁ h12 c x hc⟩
    have hS := hgQLCh_start B ν hlim hν (fun ν' _ => hgQL B U hU ν') hcoh
    have e : hgQL B U hU ν = hgfMTU (St := hgfLS ν) (fun Q U h => hgfLS_spec hν Q U h) hS := by
      rw [hgQL_limit B U hU hlim]; unfold hgQLLim; rw [dif_pos ⟨hν, hcoh⟩]
    by_cases hcS : c < hdNx (ω + ν) B.Q
    · rw [hgQL_NxQ B ν hν] at hcS
      obtain ⟨b, hb, hcb⟩ := hgVeb_cof (hgf_lev hν).ne (B.Q_fix _ (hgf_lev hν).2) hcS
      obtain ⟨ν'', hν'', hbν⟩ := (lt_add_iff hlim.bot_lt.ne').1 hb
      have hν''1 : ν'' < Om1 := hν''.trans hν
      have hcν : c < (hgQL B U hU ν'').B := by
        rw [(hgQL_inv B U hU ν'' hν''1).1.1]; exact hcb.trans_le (hcN_mono hbν _)
      have e2 := ((hgQL_inv B U hU ν hν).2 ν'' hν''.le c 0 hcν).2
      rw [e2] at hg
      exact IH ν'' hν'' hν''1 c hcν σ hσ hσ1 hg
    · exfalso
      rw [e] at hc hg
      have h := hgQ_highN _ hS hc (not_lt.1 hcS) hσ hσ1 hg
      exact hνσ (le_add_self.trans_lt h)


/-! ## The union over all levels over `Q` -/

theorem hgQ_Om1_ne : (Om1 : Ordinal.{0}) ≠ 0 := gv_Om1_pos.ne'

/-- **Every `hgQL ν`, `ν < Ω₁`, lies below `hdNx Ω₁ Q`.** -/
theorem hgQB_gt {ν : Ordinal.{0}} (hν : ν < Om1) : (hgQL B U hU ν).B < hdNx Om1 B.Q := by
  rw [(hgQL_inv B U hU ν hν).1.1]; exact hdN_lt_Nx (gv_Om1_lim.add_one_lt (hgf_lev hν).2)

/-- **The bounds `φ(ω+ν+1, Q+1)`, `ν < Ω₁`, are cofinal in `hdNx Ω₁ Q`.** -/
theorem hgQB_cof {c : Ordinal.{0}} (hc : c < hdNx Om1 B.Q) : ∃ ν, ν < Om1 ∧ c < (hgQL B U hU ν).B := by
  obtain ⟨b, hb, hcb⟩ := hgNx_cof hgQ_Om1_ne B.Q_fix hc
  exact ⟨b, hb, by rw [(hgQL_inv B U hU b hb).1.1]; exact hcb.trans_le (hcN_mono le_add_self _)⟩

theorem hgQB_lt1 : hdNx Om1 B.Q < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen Om1 (gcG 1) = gcG 1 := gn_veb_fix hG1 (hg_Om1_lt_G 1)
  have h2 := (isNormal_veblen Om1).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt B.Q_lt1)
  rw [hfix] at h2
  exact (hdNx_min ((lt_add_one _).trans_le (right_le_veblen _ _))).trans_lt h2

theorem hgQB_E : InE (hdNx Om1 B.Q) := hdNx_E hgQ_Om1_ne _

theorem hgQB_lim : IsSuccLimit (hdNx Om1 B.Q) := ev_isSuccLimit_of_inE (hgQB_E B)

/-- The first level containing `c`. -/
noncomputable def hgQN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < Om1 ∧ c < (hgQL B U hU ν).B}

theorem hgQN_spec {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hgQL B U hU ν).B) :
    hgQN B U hU c ≤ ν ∧ hgQN B U hU c < Om1 ∧ c < (hgQL B U hU (hgQN B U hU c)).B := by
  have hne : ({ν | ν < Om1 ∧ c < (hgQL B U hU ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem hgQN_high {c : Ordinal.{0}} (hc : hdNx Om1 B.Q ≤ c) : hgQN B U hU c = 0 := by
  unfold hgQN
  have he : ({ν | ν < Om1 ∧ c < (hgQL B U hU ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hgQB_gt B U hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hgQ_R_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hgQL B U hU ν).B) (x : Ordinal.{0}) :
    (hgQL B U hU (hgQN B U hU c)).R c x = (hgQL B U hU ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hgQN_spec B U hU hν hc
  exact ((hgQL_inv B U hU ν hν).2 _ h1 c x h3).1.symm

theorem hgQ_g_eq {c ν : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hgQL B U hU ν).B) :
    (hgQL B U hU (hgQN B U hU c)).g c = (hgQL B U hU ν).g c := by
  obtain ⟨h1, -, h3⟩ := hgQN_spec B U hU hν hc
  exact ((hgQL_inv B U hU ν hν).2 _ h1 c 0 h3).2.symm

theorem hgQ_R_succ (c x : Ordinal.{0}) :
    (hgQL B U hU (hgQN B U hU (c + 1))).R (c + 1) x = (hgQL B U hU (hgQN B U hU c)).R c x + 1 := by
  rcases lt_or_ge c (hdNx Om1 B.Q) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU ((hgQB_lim B).add_one_lt h)
    rw [hgQ_R_eq B U hU hn1 hn, hgQ_R_eq B U hU hn1 ((lt_add_one c).trans hn), (hgQL B U hU n).R_succ]
  · rw [hgQN_high B U hU h, hgQN_high B U hU (h.trans (le_self_add (a := c) (b := 1))), (hgQL B U hU 0).R_succ]

theorem hgQ_g_le_succ (c : Ordinal.{0}) :
    (hgQL B U hU (hgQN B U hU c)).g c ≤ (hgQL B U hU (hgQN B U hU (c + 1))).g (c + 1) := by
  rcases lt_or_ge c (hdNx Om1 B.Q) with h | h
  · obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU ((hgQB_lim B).add_one_lt h)
    rw [hgQ_g_eq B U hU hn1 hn, hgQ_g_eq B U hU hn1 ((lt_add_one c).trans hn)]; exact (hgQL B U hU n).g_le_succ c
  · rw [hgQN_high B U hU h, hgQN_high B U hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hgQL B U hU 0).g_le_succ c

/-- **The bound field of every `hgQL ν` lies below `Z_o(x)`.** -/
theorem hgQ_Z_le {ν x : Ordinal.{0}} (hν : ν < Om1) (hx : InE x) (hx1 : x < Om1) : (hgQL B U hU ν).Z x ≤ B.Zo x := by
  rw [(hgQL_inv B U hU ν hν).1.2.2.2 x hx hx1]
  split_ifs with h
  · exact (B.evN_lt_Zo hx hx1 h).le
  · exact le_rfl

/-- **The base reading of `hgQL ν` lies below `Z_o(x)`** (`ν < x`). -/
theorem hgQ_b_lt {ν x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hν : ν < x) : (hgQL B U hU ν).b x < B.Zo x := by
  rw [(hgQL_inv B U hU ν (hν.trans hx1)).1.2.2.1 x hx hx1 (hg_lev_lt hx hx1 hν)]
  exact B.N_lt_Zo hx hx1 (hg_lev_lt hx hx1 hν)

/-- **A code of the union with gate below an `ε`-number `σ` lies in `hgQL μ`, `μ < σ`.** -/
theorem hgQ_small' {c σ : Ordinal.{0}} (hc : c < hdNx Om1 B.Q) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hgQL B U hU (hgQN B U hU c)).g c < σ) : ∃ μ, μ < σ ∧ c < (hgQL B U hU μ).B := by
  obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
  rw [hgQ_g_eq B U hU hn1 hn] at hg
  exact hgQ_small B U hU n hn1 c hn σ hσ hσ1 hg

theorem hgQ_γ_lt {μ x : Ordinal.{0}} (hx : InE x) (hμ : μ < x) (hμ1 : μ < Om1) : (hgQL B U hU μ).γ < x :=
  (hgQL_γ B U hU hμ1).trans_lt ((inE_indec hx).add_lt (omega0_lt_inE hx) hμ)

/-- **THE UNION OVER ALL LEVELS OVER `Q`**: bound `hdNx Ω₁ Q`, base gate `0`, base reading `hdNx x (P x)` (the level
`Ω₁` read as `x`), bound field `evZ(hdNx x (P x)) < Γ_{x+2}`. -/
noncomputable def hgQU : HgVD where
  B := hdNx Om1 B.Q
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := fun c x => (hgQL B U hU (hgQN B U hU c)).R c x
  g := fun c => (hgQL B U hU (hgQN B U hU c)).g c
  b := B.Zo
  ba := B.Zo
  ix := hdNx Om1 B.Q
  Z := fun x => evZ (B.Zo x)
  B_E := hgQB_E B
  G_le := B.G_lt.le.trans (hdNx_gt _ _).le
  B_lt1 := hgQB_lt1 B
  B_ix := (hdNx_fix hg_one_lt_Om1 _).symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_G1 := fun x hx hx1 => gw_evZ_lt1 hx hx1 (B.Zo_lt1 hx hx1)
  ix_mem := fun S a b ha _ => B.Qn_mem S ha
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    rw [hgQ_g_eq B U hU hn1 hn]; exact (hgQL B U hU n).g_lt c hn
  g_zero := by rw [hgQ_g_eq B U hU gv_Om1_pos (hgQL B U hU 0).B_pos]; exact (hgQL B U hU 0).g_zero
  g_nat := fun k => by
    rw [hgQ_g_eq B U hU gv_Om1_pos ((hgQL B U hU 0).nat_lt_B k)]; exact (hgQL B U hU 0).g_nat k
  g_E := by rw [hgQ_g_eq B U hU gv_Om1_pos (hgQL B U hU 0).E_lt_B]; exact (hgQL B U hU 0).g_E
  g_lowE := fun c hc => by
    rw [hgQ_g_eq B U hU gv_Om1_pos (hc.trans (hgQL B U hU 0).E_lt_B)]; exact (hgQL B U hU 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU h
    rw [hgQ_g_eq B U hU hn1 hn]; exact (hgQL B U hU n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hxy
    have hx : x < (hgQL B U hU n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (hgQL B U hU n).B := lt_of_le_of_lt le_add_self hn
    show (hgQL B U hU (hgQN B U hU (x + y))).g (x + y) < Z
    rw [hgQ_g_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hx] at hgx; rw [hgQ_g_eq B U hU hn1 hy] at hgy
    exact (hgQL B U hU n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hy
    have hy' : y < (hgQL B U hU n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (hgQL B U hU (hgQN B U hU (ω ^ y))).g (ω ^ y) < Z
    rw [hgQ_g_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hy'] at hg
    exact (hgQL B U hU n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hcB
    show (hgQL B U hU (hgQN B U hU c)).g c < Z
    rw [hgQ_g_eq B U hU hn1 hn]
    exact (hgQL B U hU n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hgQB_gt B U hU hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    have hc' : c < (hgQL B U hU n).B := (lt_add_one c).trans hn
    show (hgQL B U hU (hgQN B U hU (c + 1))).g (c + 1) < Z
    rw [hgQ_g_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hc'] at hg
    exact (hgQL B U hU n).g_succ Z hZ c hn hg
  g_le_succ := hgQ_g_le_succ B U hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact (hgQL B U hU n).mem S a b ha c hn hg
  R_zero := fun x => by rw [hgQ_R_eq B U hU gv_Om1_pos (hgQL B U hU 0).B_pos]; exact (hgQL B U hU 0).R_zero x
  R_nat := fun k x => by
    rw [hgQ_R_eq B U hU gv_Om1_pos ((hgQL B U hU 0).nat_lt_B k)]; exact (hgQL B U hU 0).R_nat k x
  R_E := fun x => by rw [hgQ_R_eq B U hU gv_Om1_pos (hgQL B U hU 0).E_lt_B]; exact (hgQL B U hU 0).R_E x
  R_succ := hgQ_R_succ B U hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    show 0 < (hgQL B U hU (hgQN B U hU c)).R c x
    rw [hgQ_R_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact (hgQL B U hU n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    show ω ≤ (hgQL B U hU (hgQN B U hU c)).R c x
    rw [hgQ_R_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact (hgQL B U hU n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    show (hgQL B U hU (hgQN B U hU c)).R c x < B.Zo x
    rw [hgQ_R_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact ((hgQL B U hU n).R_lt_Z x hx hx1 c hn hg).trans_le (hgQ_Z_le B U hU hn1 hx hx1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    show (hgQL B U hU (hgQN B U hU c)).R c x < evZ (B.Zo x)
    rw [hgQ_R_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact (((hgQL B U hU n).R_lt_Z x hx hx1 c hn hg).trans_le (hgQ_Z_le B U hU hn1 hx hx1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    have hd : d < (hgQL B U hU n).B := hdc.trans hn
    show (hgQL B U hU (hgQN B U hU d)).R d x < (hgQL B U hU (hgQN B U hU c)).R c x
    rw [hgQ_R_eq B U hU hn1 hn, hgQ_R_eq B U hU hn1 hd]; rw [hgQ_g_eq B U hU hn1 hn] at hgc
    rw [hgQ_g_eq B U hU hn1 hd] at hgd
    exact (hgQL B U hU n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    rw [hgQ_R_eq B U hU hn1 hn] at hν; rw [hgQ_g_eq B U hU hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hgQL B U hU n).cof x hx hx1 c hn hg ν hν
    have hd : d < (hgQL B U hU n).B := hdc.trans hn
    exact ⟨d, hdc, by show (hgQL B U hU (hgQN B U hU d)).g d < x; rw [hgQ_g_eq B U hU hn1 hd]; exact hgd,
      by show ν ≤ (hgQL B U hU (hgQN B U hU d)).R d x; rw [hgQ_R_eq B U hU hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    have hν' : ν < hdNx x (B.P x) := by rw [← B.Zo_eq hx]; exact hν
    obtain ⟨b, hb, hνb⟩ := hgNx_cof hx.pos.ne' (B.P_fix hx hx1) hν'
    have hb1 : b < Om1 := hb.trans hx1
    have hνb' : ν < (hgQL B U hU b).b x := by
      rw [(hgQL_inv B U hU b hb1).1.2.2.1 x hx hx1 (hg_lev_lt hx hx1 hb)]
      exact hνb.trans_le (hcN_mono le_add_self _)
    obtain ⟨d, hd, hgd, hνd⟩ := (hgQL B U hU b).b_cof x hx hx1 (hgQ_γ_lt B U hU hx hb hb1) ν hνb'
    exact ⟨d, hd.trans (hgQB_gt B U hU hb1),
      by show (hgQL B U hU (hgQN B U hU d)).g d < x; rw [hgQ_g_eq B U hU hb1 hd]; exact hgd,
      by show ν < (hgQL B U hU (hgQN B U hU d)).R d x; rw [hgQ_R_eq B U hU hb1 hd]; exact hνd⟩
  b_E := fun x hx _ _ => by rw [B.Zo_eq hx]; exact hdNx_E hx.pos.ne' _
  x_lt_b := fun x hx hx1 _ => by rw [B.Zo_eq hx]; exact (B.P_gt hx hx1).trans (hdNx_gt _ _)
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (B.Zo_fix1 x)
    (by rw [B.Zo_eq hx]; exact (B.P_gt hx hx1).trans (hdNx_gt _ _)) (B.Zo_lt1 hx hx1)
  ba_lt := fun x hx hx1 _ => B.Zo_lt1 hx hx1
  b_Z := fun _ _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun σ ρ hB _ => by
    rw [B.Zo_eq hB.2.1, B.Zo_eq hB.1]; exact B.Pn_pi hB
  ba_pi := fun σ ρ hB _ => by
    rw [B.Zo_eq hB.2.1, B.Zo_eq hB.1]; exact B.Pn_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    show (hgQL B U hU (hgQN B U hU c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((hgQL B U hU (hgQN B U hU c)).R c ρ) = (hgQL B U hU (hgQN B U hU c)).R c σ
    rw [hgQ_R_eq B U hU hn1 hn, hgQ_R_eq B U hU hn1 hn]; rw [hgQ_g_eq B U hU hn1 hn] at hg
    exact (hgQL B U hU n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hgQ_small' B U hU hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (hgQL B U hU (hgQN B U hU d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (hgQL B U hU (hgQN B U hU d)).R d ρ) = ω ^ P' * (hgQL B U hU (hgQN B U hU d)).R d σ
    rw [hgQ_R_eq B U hU hμ1 hdμ, hgQ_R_eq B U hU hμ1 hdμ]; rw [hgQ_g_eq B U hU hμ1 hdμ] at hg
    exact (hgQL B U hU μ).dig σ ρ hB (hgQ_γ_lt B U hU hB.1 hμσ hμ1) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hgQ_b_lt B U hU hB.2.1 hB.2.2.2 (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := hgQB_cof B U hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hgQL B U hU n).ld c hl hn
    have hcpn : cp < (hgQL B U hU n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (hgQL B U hU (hgQN B U hU cp)).g cp ≤ (hgQL B U hU (hgQN B U hU c)).g c
      rw [hgQ_g_eq B U hU hn1 hn, hgQ_g_eq B U hU hn1 hcpn]; exact hgcp
    · have hg' : (hgQL B U hU n).g c < x := by rw [← hgQ_g_eq B U hU hn1 hn]; exact hg
      show (hgQL B U hU (hgQN B U hU c)).R c x = _ ∧ _
      rw [hgQ_R_eq B U hU hn1 hn, hgQ_R_eq B U hU hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hgQ_g_eq B U hU hn1 hn]; exact hg

theorem hgQU_B : (hgQU B U hU).B = hdNx Om1 B.Q := rfl

theorem hgQU_γ : (hgQU B U hU).γ = 0 := rfl

theorem hgQU_b (x : Ordinal.{0}) : (hgQU B U hU).b x = B.Zo x := rfl

theorem hgQU_Z (x : Ordinal.{0}) : (hgQU B U hU).Z x = evZ (B.Zo x) := rfl

theorem hgQU_ix : (hgQU B U hU).ix = hdNx Om1 B.Q := rfl

/-- **The union extends every `hgQL ν`, `ν < Ω₁`** (readings). -/
theorem hgQU_R {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hgQL B U hU ν).B) (x : Ordinal.{0}) :
    (hgQU B U hU).R c x = (hgQL B U hU ν).R c x := hgQ_R_eq B U hU hν hc x

/-- **The union extends every `hgQL ν`, `ν < Ω₁`** (gates). -/
theorem hgQU_g {ν c : Ordinal.{0}} (hν : ν < Om1) (hc : c < (hgQL B U hU ν).B) :
    (hgQU B U hU).g c = (hgQL B U hU ν).g c := hgQ_g_eq B U hU hν hc

include U hU in
/-- **`hdNx Ω₁ Q` IS LOCATED**: `Λ⁺ = ι(Γ(hdNx Ω₁ Q)·ω)`, `P(…) < L(0)` (UNCONDITIONAL beyond `B`, `U`). -/
theorem hgQU_loc (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hdNx Om1 B.Q) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hdNx Om1 B.Q) * ω) ∧ Pv S (gcG (hdNx Om1 B.Q) * ω) < Nc.ncL S 0 :=
  hgV_locD (hgQU B U hU) S (hg_K_pos S)

include U hU in
/-- **ENUM-REACH below `ι(Γ(hdNx Ω₁ Q)·ω)`.** -/
theorem hgQU_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (hdNx Om1 B.Q) * ω)) : CdUpper S l ∧ CdLower S l :=
  hgV_locD_enum (hgQU B U hU) S (hg_K_pos S) hr hl

include U hU in
/-- **CapV below `ι(Γ(hdNx Ω₁ Q)·ω)`.** -/
theorem hgQU_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (hdNx Om1 B.Q) * ω)) : CdCapV S l :=
  hgV_locD_capV (hgQU B U hU) S (hg_K_pos S) hr hl

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hg
