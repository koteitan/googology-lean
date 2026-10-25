import Googology.Trans.PoR.InaccPsi.R2.GzSU

/-!
# THE RECURSION OVER THE `ζ`-INDICES `λ < ε₀`: THE UNIONS AT `ζ_{G+1+λ}` FOR EVERY CONSTANT `λ`, LIMITS INCLUDED

For a constant `λ < ε₀` (below every base) the stage `gzPBl λ` has the index base `Q_λ = φ(2, G + 1 + λ) =
ζ_{G+1+λ}` and its reading `P_λ(x) = ϑˣ(Ω₁·2 + Γ_{x+1} + λ) = φ(2, i₀(x) + λ) = ζ_{Γ_{x+1}+1+λ}` (`gz_PBl_P`, through
`Gz.gz_glA2V`; `P_λ(x) < B₃(x)`).  One recursion (`gzLU`) gives the start of every stage:

* `gzLU 0 = GzVD.ofW gwZU` (the union at `ζ_{G+1}`);
* `gzLU (λ+1)` is the self-read union `Gz.gzSU` of the stage `λ` started at `gzLU λ` (index `ζ_{G+1+λ+1}`);
* at a limit `λ`, `gzLU λ` is the union of all `gzLU μ`, `μ < λ` (`GzLFam.U`; all have base gate `0`): bound
  `ζ_{G+1+λ}`, base reading `ζ_{Γ_{x+1}+1+λ}`, base gate `0`; its base data are Lemma EXACT for `P_λ` (`GzPB.P_pi`),
  `ε_{P+1} = ϑˣ(Ω₁ + P)` (`Gz.gz_eN_fix`), and the cofinality of `P_μ(x)`, `μ < λ`, in `P_λ(x)` (continuity of
  `φ(2, ·)`).
  **The limit `ζ`-points `ζ_{G+λ}` (`λ` a limit) are passed**: Lemma IMG there is `Gz.gzI_limZ`, used through
  `Gz.gzPkg_of_exB3` in the reading system of every `GzVD`.

* `gzI0`, `gzI0_spec`, `gz_PBl_veb`, `gzPBl` (**the stage at `λ`**), `gzPBl_Q`, `gz_PBl_P`, `gzPBl_succQ`,
  `gzPBl_succP`;
* `GzLInv`, `GzLFam`, `GzLFam.U` (**THE UNION AT A LIMIT `ζ`-INDEX**), `gzLStep`, `gzLExt`, `gzLLimD`, `gzLU`
  (**THE RECURSION**), `gzL_inv` (**every `gzLU λ`, `λ < ε₀`, starts the stage `λ`, and later starts extend earlier
  ones**), `gzLU_start`, `gzLD` (the systems of the stage `λ`), `gzLD_B`.

No new axiom.  New definitions: `gzI0`, `gzPBl`, `GzLInv`, `GzLFam`, `GzLFam.N`, `GzLFam.R`, `GzLFam.g`, `GzLFam.U`,
`gzLStep`, `gzLExt`, `gzLLimD`, `gzLU`, `gzLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The stage at a constant `ζ`-index `λ < ε₀` -/

/-- **`i₀(x)`**: `φ(2, i₀(x)) = ζ_{Γ_{x+1}+1}`. -/
noncomputable def gzI0 (x : Ordinal.{0}) : Ordinal.{0} := Classical.choose (gw_LuP2 (lgG x))

theorem gzI0_spec (x : Ordinal.{0}) : veblen 2 (gzI0 x) = evZ (lgG x) := Classical.choose_spec (gw_LuP2 (lgG x))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gz_I0_add_lt {l : Ordinal.{0}} (hl : l < ε₀) : gzI0 x + l < gzB3 x :=
  (inE_indec (gzB3_E x)).add_lt ((gz_i0_lt hx hx1 (gzI0_spec x)).trans (gzZ1_lt_B3 x))
    (hl.trans_le ((go_eps0_le hx).trans ((gwZn_gt hx hx1 1).trans (gz_Zn_lt_B3 hx hx1 1)).le))

theorem gz_PBl_veb_lt {l : Ordinal.{0}} (hl : l < ε₀) : veblen 2 (gzI0 x + l) < gzB3 x := by
  have h := (isNormal_veblen 2).strictMono (gz_I0_add_lt hx hx1 hl)
  rwa [gzB3_fix] at h

theorem gz_lt_l_lt {l : Ordinal.{0}} (hl : l < ε₀) : lgG x + l < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (mg_lgG_lt_G1 hx hx1)
    (hl.trans_le ((go_eps0_le hx).trans (gm1_facts hx hx1).2.1.le))

/-- **`ϑˣ(Ω₁·2 + Γ_{x+1} + λ) = φ(2, i₀(x) + λ)`** for every `λ < ε₀`. -/
theorem gz_PBl_veb {l : Ordinal.{0}} (hl : l < ε₀) : glA 2 (lgG x + l) x = veblen 2 (gzI0 x + l) :=
  gz_glA2V hx hx1 (gzI0_spec x) l (gz_lt_l_lt hx hx1 hl) fun ν' h' _ =>
    gz_nofix_B3 hx hx1 (gzI0_spec x) le_self_add
      (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt (gz_PBl_veb_lt hx hx1 hl))

end Base

/-- **The stage at the `ζ`-index `λ < ε₀`**: `Q_λ = φ(2, G + 1 + λ)`, `t_P(x) = Γ_{x+1} + λ`. -/
noncomputable def gzPBl (l : Ordinal.{0}) (hl : l < ε₀) : GzPB where
  jQ := gcG 0 + 1 + l
  tP := fun x => lgG x + l
  jQ_mem := fun S a b ha => CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha))
    (gr_cst_mem ha b l (hl.trans (epsilon_zero_lt_gamma 1)))
  jQ_cl := fun Z hZ => GxCl.add (GxCl.add (GxCl.atom (Set.mem_singleton _)) (GxCl.small (gw_one_lt_SC hZ)))
    (GxCl.small (hl.trans_le (go_eps0_le (Low.opow_eq_self_of_SC hZ))))
  G_lt_Q := by
    have h := (isNormal_veblen 2).strictMono
      ((lt_add_one (gcG 0)).trans_le (le_self_add : gcG 0 + 1 ≤ gcG 0 + 1 + l))
    rwa [gn_veb_fix (gcG_SC 0) gw_two_lt_G] at h
  Q_lt1 := by
    have hG1 := gcG_SC 1
    have hE : InE (gcG 1) := Low.opow_eq_self_of_SC hG1
    have hl1 : l < gcG 1 := hl.trans_le (go_eps0_le hE)
    refine hG1.2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ (hG1.add_one_lt ?_)
    exact (inE_indec hE).add_lt (hG1.add_one_lt (gcG_lt zero_lt_one)) hl1
  tP_lt := fun x hx hx1 =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (gz_lt_l_lt hx hx1 hl)
  tP_pi := fun σ ρ hB => by
    have hlσ : l < σ := hl.trans_le (go_eps0_le hB.1)
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hlσ)
    rw [g2, pi_lt hB hlσ] at s2
    exact ⟨s1, s2⟩
  P_B3 := fun x hx hx1 => by
    show glA 2 (lgG x + l) x < gzB3 x
    rw [gz_PBl_veb hx hx1 hl]; exact gz_PBl_veb_lt hx hx1 hl

theorem gzPBl_Q (l : Ordinal.{0}) (hl : l < ε₀) : (gzPBl l hl).Q = veblen 2 (gcG 0 + 1 + l) := rfl

theorem gz_PBl_P (l : Ordinal.{0}) (hl : l < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gzPBl l hl).P x = veblen 2 (gzI0 x + l) := gz_PBl_veb hx hx1 hl

theorem gzPBl_succQ (l : Ordinal.{0}) (hl : l < ε₀) (hl1 : l + 1 < ε₀) :
    (gzPBl (l + 1) hl1).Q = evZ (gzPBl l hl).Q := by
  rw [gzPBl_Q, gzPBl_Q, gz_evZ_veb2, add_assoc (gcG 0 + 1)]

theorem gzPBl_succP (l : Ordinal.{0}) (hl : l < ε₀) (hl1 : l + 1 < ε₀) {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) : (gzPBl (l + 1) hl1).P x = evZ ((gzPBl l hl).P x) := by
  rw [GzPB.evP _ hx hx1]
  show glA 2 (lgG x + (l + 1)) x = glA 2 (lgG x + l + 1) x
  rw [add_assoc]

theorem gzPBl_P_le {l l' : Ordinal.{0}} (hl : l < ε₀) (hl' : l' < ε₀) (h : l ≤ l') {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) : (gzPBl l hl).P x ≤ (gzPBl l' hl').P x := by
  rw [gz_PBl_P l hl hx hx1, gz_PBl_P l' hl' hx hx1]
  exact (isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h)

theorem gzPBl_Q_lt {l l' : Ordinal.{0}} (hl : l < ε₀) (hl' : l' < ε₀) (h : l < l') :
    (gzPBl l hl).Q < (gzPBl l' hl').Q := by
  rw [gzPBl_Q, gzPBl_Q]; exact (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 h)

/-- The start at `λ = 0` is the union at `ζ_{G+1}`. -/
theorem gzL_start0 (h0 : (0 : Ordinal.{0}) < ε₀) : GzSStart (gzPBl 0 h0) (GzVD.ofW gwZU) where
  ix := by rw [gzPBl_Q, add_zero]; exact gwZ_eq_veb2
  γ := rfl
  b := fun x hx hx1 => by
    show evZ (lgG x) = glA 2 (lgG x + 0) x
    rw [add_zero]; exact (gw_glA2_eq hx hx1).symm
  Z := fun x hx hx1 => by
    show evZ (evZ (lgG x)) = evZ (glA 2 (lgG x + 0) x)
    rw [add_zero, gw_glA2_eq hx hx1]

/-! ## The union at a limit `ζ`-index -/

/-- **The invariant of the starts below `λ`.** -/
structure GzLInv (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Prop where
  st : ∀ μ (hμ : μ < ε₀), μ < l → GzSStart (gzPBl μ hμ) (F μ)
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

theorem gzL_B {F : Ordinal.{0} → GzVD} {μ : Ordinal.{0}} (hμ : μ < ε₀) (h : GzSStart (gzPBl μ hμ) (F μ)) :
    (F μ).B = (gzPBl μ hμ).Q := by
  rw [(F μ).B_ix, h.ix]; exact (gzPBl μ hμ).Q_fix

/-- **The family of all starts below a limit `λ < ε₀`.** -/
structure GzLFam where
  l : Ordinal.{0}
  F : Ordinal.{0} → GzVD
  l_lim : IsSuccLimit l
  l_lt : l < ε₀
  H : GzLInv l F

namespace GzLFam

variable (L : GzLFam)

theorem lt_e {μ : Ordinal.{0}} (h : μ < L.l) : μ < ε₀ := h.trans L.l_lt

theorem B_eq {μ : Ordinal.{0}} (h : μ < L.l) : (L.F μ).B = (gzPBl μ (L.lt_e h)).Q :=
  gzL_B (L.lt_e h) (L.H.st μ (L.lt_e h) h)

theorem γ_eq {μ : Ordinal.{0}} (h : μ < L.l) : (L.F μ).γ = 0 := (L.H.st μ (L.lt_e h) h).γ

/-- The bound of the union. -/
noncomputable def BU : Ordinal.{0} := (gzPBl L.l L.l_lt).Q

theorem B_lt {μ : Ordinal.{0}} (h : μ < L.l) : (L.F μ).B < L.BU := by
  rw [L.B_eq h]; exact gzPBl_Q_lt _ _ h

theorem B_cof {c : Ordinal.{0}} (hc : c < L.BU) : ∃ μ, μ < L.l ∧ c < (L.F μ).B := by
  have hlim : IsSuccLimit (gcG 0 + 1 + L.l) := isSuccLimit_add _ L.l_lim
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hlim).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff L.l_lim.bot_lt.ne').1 ht
  exact ⟨d, hd, by rw [L.B_eq hd, gzPBl_Q]; exact hct.trans_le ((isNormal_veblen 2).monotone htd)⟩

/-- The first member containing `c`. -/
noncomputable def N (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < L.l ∧ c < (L.F μ).B}

theorem N_spec {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) :
    L.N c ≤ ν ∧ L.N c < L.l ∧ c < (L.F (L.N c)).B := by
  have hne : ({μ | μ < L.l ∧ c < (L.F μ).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem N_high {c : Ordinal.{0}} (hc : L.BU ≤ c) : L.N c = 0 := by
  unfold GzLFam.N
  have he : ({μ | μ < L.l ∧ c < (L.F μ).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (L.B_lt hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (L.F (L.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (L.F (L.N c)).g c

theorem R_eq {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) (x : Ordinal.{0}) :
    L.R c x = (L.F ν).R c x := by
  obtain ⟨h1, -, h3⟩ := L.N_spec hν hc
  exact (L.H.cohR _ _ h1 hν c x h3).symm

theorem g_eq {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.g c = (L.F ν).g c := by
  obtain ⟨h1, -, h3⟩ := L.N_spec hν hc
  exact (L.H.cohg _ _ h1 hν c h3).symm

theorem BU_E : InE L.BU := (gzPBl L.l L.l_lt).Q_E

theorem BU_lim : IsSuccLimit L.BU := ev_isSuccLimit_of_inE L.BU_E

theorem R_succ' (c x : Ordinal.{0}) : L.R (c + 1) x = L.R c x + 1 := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.R_eq hn1 hn, L.R_eq hn1 ((lt_add_one c).trans hn), (L.F n).R_succ]
  · unfold GzLFam.R
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1))), (L.F 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : L.g c ≤ L.g (c + 1) := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.g_eq hn1 hn, L.g_eq hn1 ((lt_add_one c).trans hn)]; exact (L.F n).g_le_succ c
  · unfold GzLFam.g
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (L.F 0).g_le_succ c

theorem l_pos : 0 < L.l := L.l_lim.bot_lt

theorem Z_le {μ x : Ordinal.{0}} (hμ : μ < L.l) (hx : InE x) (hx1 : x < Om1) :
    (L.F μ).Z x ≤ (gzPBl L.l L.l_lt).P x := by
  have hμ1 : μ + 1 < ε₀ := (ev_isSuccLimit_of_inE (omega0_opow_epsilon 0)).add_one_lt (L.lt_e hμ)
  rw [(L.H.st μ (L.lt_e hμ) hμ).Z x hx hx1, ← gzPBl_succP μ (L.lt_e hμ) hμ1 hx hx1]
  exact gzPBl_P_le hμ1 L.l_lt (Order.add_one_le_of_lt hμ) hx hx1

theorem b_le {μ x : Ordinal.{0}} (hμ : μ < L.l) (hx : InE x) (hx1 : x < Om1) :
    (L.F μ).b x ≤ (gzPBl L.l L.l_lt).P x := by
  rw [(L.H.st μ (L.lt_e hμ) hμ).b x hx hx1]
  exact gzPBl_P_le (L.lt_e hμ) L.l_lt hμ.le hx hx1

/-- **THE UNION AT A LIMIT `ζ`-INDEX `λ`**: bound `ζ_{G+1+λ}`, base gate `0`, base reading `P_λ(x) =
ζ_{Γ_{x+1}+1+λ}`, bound field `evZ(P_λ(x))`. -/
noncomputable def U : GzVD where
  B := L.BU
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := L.R
  g := L.g
  b := (gzPBl L.l L.l_lt).P
  ba := (gzPBl L.l L.l_lt).P
  ix := (gzPBl L.l L.l_lt).Q
  Z := fun x => evZ ((gzPBl L.l L.l_lt).P x)
  B_E := L.BU_E
  G_le := (gzPBl L.l L.l_lt).G_le_Q
  B_lt1 := (lt_evZ _).trans (gzPBl L.l L.l_lt).evQ_lt1
  B_ix := (gzPBl L.l L.l_lt).Q_fix.symm
  Z_fix := fun _ _ _ => epsilon_evZ _
  Z_B3 := fun x hx hx1 => ((gzPBl L.l L.l_lt).evP_B3 hx hx1).le
  ix_mem := fun S a b ha _ => (gzPBl L.l L.l_lt).Q_mem S ha
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.g_eq hn1 hn]; exact (L.F n).g_lt c hn
  g_zero := by rw [L.g_eq L.l_pos (L.F 0).B_pos]; exact (L.F 0).g_zero
  g_nat := fun k => by rw [L.g_eq L.l_pos ((L.F 0).nat_lt_B k)]; exact (L.F 0).g_nat k
  g_E := by rw [L.g_eq L.l_pos (L.F 0).E_lt_B]; exact (L.F 0).g_E
  g_lowE := fun c hc => by rw [L.g_eq L.l_pos (hc.trans (L.F 0).E_lt_B)]; exact (L.F 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof h
    rw [L.g_eq hn1 hn]; exact (L.F n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hxy
    have hx : x < (L.F n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (L.F n).B := lt_of_le_of_lt le_add_self hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hx] at hgx; rw [L.g_eq hn1 hy] at hgy
    exact (L.F n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hy
    have hy' : y < (L.F n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hy'] at hg
    exact (L.F n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hcB
    rw [L.g_eq hn1 hn]
    exact (L.F n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (L.B_lt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    have hc' : c < (L.F n).B := (lt_add_one c).trans hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hc'] at hg
    exact (L.F n).g_succ Z hZ c hn hg
  g_le_succ := L.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.g_eq hn1 hn] at hg
    exact (L.F n).mem S a b ha c hn hg
  R_zero := fun x => by rw [L.R_eq L.l_pos (L.F 0).B_pos]; exact (L.F 0).R_zero x
  R_nat := fun k x => by rw [L.R_eq L.l_pos ((L.F 0).nat_lt_B k)]; exact (L.F 0).R_nat k x
  R_E := fun x => by rw [L.R_eq L.l_pos (L.F 0).E_lt_B]; exact (L.F 0).R_E x
  R_succ := L.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact ((L.F n).R_lt_Z x hx hx1 c hn hg).trans_le (L.Z_le hn1 hx hx1)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (((L.F n).R_lt_Z x hx hx1 c hn hg).trans_le (L.Z_le hn1 hx hx1)).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    have hd : d < (L.F n).B := hdc.trans hn
    rw [L.R_eq hn1 hn, L.R_eq hn1 hd]; rw [L.g_eq hn1 hn] at hgc; rw [L.g_eq hn1 hd] at hgd
    exact (L.F n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn] at hν; rw [L.g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (L.F n).cof x hx hx1 c hn hg ν hν
    have hd : d < (L.F n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [L.g_eq hn1 hd]; exact hgd, by rw [L.R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    rw [gz_PBl_P L.l L.l_lt hx hx1] at hν
    have hlim : IsSuccLimit (gzI0 x + L.l) := isSuccLimit_add _ L.l_lim
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hlim).1 hν
    obtain ⟨d, hd, htd⟩ := (lt_add_iff L.l_pos.ne').1 ht
    have hb : ν < (L.F d).b x := by
      rw [(L.H.st d (L.lt_e hd) hd).b x hx hx1, gz_PBl_P d (L.lt_e hd) hx hx1]
      exact hνt.trans_le ((isNormal_veblen 2).monotone htd)
    obtain ⟨c, hc, hgc, hνc⟩ := (L.F d).b_cof x hx hx1 (by rw [L.γ_eq hd]; exact hx.pos) ν hb
    exact ⟨c, hc.trans (L.B_lt hd), by rw [L.g_eq hd hc]; exact hgc, by rw [L.R_eq hd hc]; exact hνc⟩
  b_E := fun x hx hx1 _ => ((gzPBl L.l L.l_lt).P_facts hx hx1).2.2.2
  x_lt_b := fun x hx hx1 _ => (gzPBl L.l L.l_lt).P_gt hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 ((gzPBl L.l L.l_lt).P_fix hx hx1) ((gzPBl L.l L.l_lt).P_gt hx hx1)
    ((gzPBl L.l L.l_lt).P_lt hx hx1)
  ba_lt := fun x hx hx1 _ => (gzPBl L.l L.l_lt).P_lt hx hx1
  b_Z := fun x _ _ _ => go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB _ => (gzPBl L.l L.l_lt).P_pi hB
  ba_pi := fun _ _ hB _ => (gzPBl L.l L.l_lt).P_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn, L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hd
    rw [L.R_eq hn1 hn, L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).dig σ ρ hB (by rw [L.γ_eq hn1]; exact hB.1.pos) d hn hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (L.b_le hn1 hB.2.1 hB.2.2.2)))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (L.F n).ld c hl hn
    have hcpn : cp < (L.F n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [L.g_eq hn1 hn, L.g_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← L.g_eq hn1 hn]; exact hg)⟩
    rw [L.g_eq hn1 hn] at hg
    rw [L.R_eq hn1 hn, L.R_eq hn1 hcpn]
    exact hdec x hx hx1 hg

theorem U_R {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) (x : Ordinal.{0}) :
    L.U.R c x = (L.F ν).R c x := L.R_eq hν hc x

theorem U_g {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.U.g c = (L.F ν).g c := L.g_eq hν hc

/-- **The union at the limit `ζ`-index `λ` starts the stage `λ`.** -/
theorem U_start : GzSStart (gzPBl L.l L.l_lt) L.U where
  ix := rfl
  γ := rfl
  b := fun _ _ _ => rfl
  Z := fun _ _ _ => rfl

end GzLFam

/-! ## The recursion -/

/-- The successor step: the self-read union of the stage `λ` started at `U` (when `U` starts it). -/
noncomputable def gzLStep (l : Ordinal.{0}) (U : GzVD) : GzVD := by
  classical
  exact if h : ∃ hl : l < ε₀, GzSStart (gzPBl l hl) U then gzSU h.choose_spec else U

/-- The family of the earlier values, extended by the start at `0`. -/
noncomputable def gzLExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GzVD) (β : Ordinal.{0}) : GzVD :=
  if h : β < l then IH β h else GzVD.ofW gwZU

open Classical in
/-- The limit step: the union of all earlier starts when the invariant holds. -/
noncomputable def gzLLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GzVD) : GzVD :=
  if H : l < ε₀ ∧ GzLInv l (gzLExt l IH) then (GzLFam.mk l (gzLExt l IH) hl H.1 H.2).U else GzVD.ofW gwZU

/-- **THE RECURSION OVER THE `ζ`-INDICES**: `gzLU λ` is the start of the stage `λ` (the union at `ζ_{G+1+λ}`). -/
noncomputable def gzLU (ν : Ordinal.{0}) : GzVD :=
  Ordinal.limitRecOn (motive := fun _ => GzVD) ν (GzVD.ofW gwZU) gzLStep gzLLimD

theorem gzLU_zero : gzLU 0 = GzVD.ofW gwZU := by unfold gzLU; rw [Ordinal.limitRecOn_zero]

theorem gzLU_succ (ν : Ordinal.{0}) : gzLU (ν + 1) = gzLStep ν (gzLU ν) := by
  unfold gzLU; rw [Ordinal.limitRecOn_add_one]

theorem gzLU_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gzLU l = gzLLimD l hl (fun β _ => gzLU β) := by
  unfold gzLU; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gzLExt_eq {l β : Ordinal.{0}} (h : β < l) : gzLExt l (fun β _ => gzLU β) β = gzLU β := by
  unfold gzLExt; rw [dif_pos h]

theorem gzLInv_congr {l : Ordinal.{0}} {F G : Ordinal.{0} → GzVD} (H : GzLInv l F) (hFG : ∀ β, β < l → G β = F β) :
    GzLInv l G where
  st := fun μ hμ h => by rw [hFG μ h]; exact H.st μ hμ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc

/-- The successor value when `gzLU ν` starts the stage `ν`. -/
theorem gzLU_succ_eq {ν : Ordinal.{0}} (hν : ν < ε₀) (h : GzSStart (gzPBl ν hν) (gzLU ν)) :
    gzLU (ν + 1) = gzSU h := by
  rw [gzLU_succ]; unfold gzLStep
  rw [dif_pos ⟨hν, h⟩]

theorem gzLU_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < ε₀) (H : GzLInv l gzLU) :
    gzLU l = (GzLFam.mk l (gzLExt l fun β _ => gzLU β) hl hle (gzLInv_congr H fun β h => gzLExt_eq h)).U := by
  rw [gzLU_limit hl]; unfold gzLLimD; rw [dif_pos ⟨hle, gzLInv_congr H fun β h => gzLExt_eq h⟩]

/-- **THE INVARIANT**: every `gzLU λ`, `λ < ε₀`, starts the stage `λ`, and later starts extend earlier ones. -/
theorem gzL_inv : ∀ ν : Ordinal.{0}, ν < ε₀ → GzLInv (ν + 1) gzLU := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro h0
    refine ⟨fun μ hμ h => ?_, fun β γ hβγ h c x _ => ?_, fun β γ hβγ h c _ => ?_⟩
    · have : μ = 0 := Order.lt_one_iff.1 (by rwa [zero_add] at h)
      subst this; rw [gzLU_zero]; exact gzL_start0 hμ
    · have hγ : γ = 0 := Order.lt_one_iff.1 (by rwa [zero_add] at h)
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
    · have hγ : γ = 0 := Order.lt_one_iff.1 (by rwa [zero_add] at h)
      have hβ : β = 0 := le_antisymm (hγ ▸ hβγ) zero_le
      rw [hγ, hβ]
  | add_one μ ih =>
    intro hν
    have hμ : μ < ε₀ := (lt_add_one μ).trans hν
    have H := ih hμ
    have hst : GzSStart (gzPBl μ hμ) (gzLU μ) := H.st μ hμ (lt_add_one μ)
    have e := gzLU_succ_eq hμ hst
    have hstS : GzSStart (gzPBl (μ + 1) hν) (gzLU (μ + 1)) := by
      rw [e]
      exact gzSU_start hst (gzPBl (μ + 1) hν) (gzPBl_succQ μ hμ hν)
        (fun x hx hx1 => gzPBl_succP μ hμ hν hx hx1)
    have hext : ∀ c x, c < (gzLU μ).B → (gzLU (μ + 1)).R c x = (gzLU μ).R c x := fun c x hc => by
      rw [e, gzSU_R hst (gzS_zero_lt2 (Bp := gzPBl μ hμ)) (by rw [gzSD_zero]; exact hc) x, gzSD_zero]
    have hextg : ∀ c, c < (gzLU μ).B → (gzLU (μ + 1)).g c = (gzLU μ).g c := fun c hc => by
      rw [e, gzSU_g hst (gzS_zero_lt2 (Bp := gzPBl μ hμ)) (by rw [gzSD_zero]; exact hc), gzSD_zero]
    refine ⟨fun β hβ h => ?_, fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h'
      · exact hstS
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hβ : β < ε₀ := lt_of_le_of_lt hβμ hμ
          have hcμ : c < (gzLU μ).B := hc.trans_le (by
            rw [gzL_B hβ (H.st β hβ (lt_of_le_of_lt hβμ (lt_add_one μ))), gzL_B hμ hst]
            rcases hβμ.lt_or_eq with h3 | h3
            · exact (gzPBl_Q_lt hβ hμ h3).le
            · subst h3; exact le_rfl)
          rw [hext c x hcμ]; exact H.cohR β μ hβμ (lt_add_one μ) c x hc
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · have hβμ : β ≤ μ := Order.lt_add_one_iff.1 h''
          have hβ : β < ε₀ := lt_of_le_of_lt hβμ hμ
          have hcμ : c < (gzLU μ).B := hc.trans_le (by
            rw [gzL_B hβ (H.st β hβ (lt_of_le_of_lt hβμ (lt_add_one μ))), gzL_B hμ hst]
            rcases hβμ.lt_or_eq with h3 | h3
            · exact (gzPBl_Q_lt hβ hμ h3).le
            · subst h3; exact le_rfl)
          rw [hextg c hcμ]; exact H.cohg β μ hβμ (lt_add_one μ) c hc
        · rfl
  | limit l hl ih =>
    intro hν
    have hIH : ∀ β, β < l → GzLInv (β + 1) gzLU := fun β h => ih β h (h.trans hν)
    have H : GzLInv l gzLU := ⟨fun μ hμ h => (hIH μ h).st μ hμ (lt_add_one μ),
      fun β γ hβγ h => (hIH γ h).cohR β γ hβγ (lt_add_one γ),
      fun β γ hβγ h => (hIH γ h).cohg β γ hβγ (lt_add_one γ)⟩
    have e := gzLU_lim_eq hl hν H
    set L := GzLFam.mk l (gzLExt l fun β _ => gzLU β) hl hν (gzLInv_congr H fun β h => gzLExt_eq h) with hL
    have hF : ∀ β, β < l → L.F β = gzLU β := fun β h => gzLExt_eq h
    refine ⟨fun β hβ h => ?_, fun β γ hβγ h c x hc => ?_, fun β γ hβγ h c hc => ?_⟩
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.st β hβ h'
      · rw [e]; exact L.U_start
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohR β γ hβγ h' c x hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · rw [e, L.U_R h'' (by rw [hF β h'']; exact hc) x, hF β h'']
        · rfl
    · rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
      · exact H.cohg β γ hβγ h' c hc
      · rcases hβγ.lt_or_eq with h'' | rfl
        · rw [e, L.U_g h'' (by rw [hF β h'']; exact hc), hF β h'']
        · rfl

/-- **`gzLU λ` STARTS THE STAGE `λ`** for every `λ < ε₀`. -/
theorem gzLU_start {l : Ordinal.{0}} (hl : l < ε₀) : GzSStart (gzPBl l hl) (gzLU l) :=
  (gzL_inv l hl).st l hl (lt_add_one l)

/-- **The systems of the stage `λ`**: `gzLD λ d` has the bound `ε_{ζ_{G+1+λ}+d}` (`d < ζ_{G+1+λ+1}`). -/
noncomputable def gzLD (l : Ordinal.{0}) (hl : l < ε₀) (d : Ordinal.{0}) : GzVD := gzSD (gzPBl l hl) (gzLU l) d

theorem gzLD_B {l d : Ordinal.{0}} (hl : l < ε₀) (hd : d < evZ (gzPBl l hl).Q) :
    (gzLD l hl d).B = veblen 1 ((gzPBl l hl).Q + d) := gzS_B (gzLU_start hl) hd

end Googology.Trans.PoR.InaccPsi.R2.Gz
