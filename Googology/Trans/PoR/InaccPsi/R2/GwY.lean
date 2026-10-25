import Googology.Trans.PoR.InaccPsi.R2.GwYCl
import Googology.Trans.PoR.InaccPsi.R2.GwZx

/-!
# THE UNION OVER ALL SMALLER INDICES ABOVE `ζ_{G+1}` (indices `ζ_{G+1} + μ`, readings below `ζ_{Γ_{x+1}+2}`)

Port of `Gw.GwYFam` (`R2.GwU`) to the systems `GwZD` with `N = 1`: the members are indexed by all `μ < λ` (`λ` a limit
below `ζ_{G+2}`), member `μ` has the bound `φ(1, ζ_{G+1} + μ)` and, above its gate, the base reading
`φ(1, ζ_{Γ_{x+1}+1} + μ_E(x))` (`μ_E` the reading of the code `μ` in the index system `E`).  The union
(`GwYFam.U`) has the bound `φ(1, ζ_{G+1} + λ)`, base gate `g_E(λ)` and base reading `φ(1, ζ_{Γ_{x+1}+1} + λ_E(x))`;
Lemma EXACT for it is `Gw.gw_b_pi_Z` (the pseudo-base `ζ_{Γ_{ρ+1}+1}`), `ε_{b+1} = ϑˣ(Ω₁ + ζ + λ_E(x) + 1)` is
`Gw.gw_b_eN_Z`, the code-gate condition is `Gw.gwY_cl_gate`.

* `GwYFam`, `GwYFam.N`, `GwYFam.R`, `GwYFam.g`, `GwYFam.small'`, `GwYFam.b_le`, `GwYFam.U` (**THE UNION**), `U_B`,
  `U_γ`, `U_N`, `U_ix`, `U_b`, `U_R`, `U_g`.

No new axiom.  New definitions: `GwYFam`, `GwYFam.N`, `GwYFam.R`, `GwYFam.g`, `GwYFam.U`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A family of systems `GwZD` (`N = 1`) over all indices `ζ_{G+1} + μ`, `μ < λ`, read by a code system `E`.** -/
structure GwYFam where
  E : GwZD
  l : Ordinal.{0}
  F : Ordinal.{0} → GwZD
  l_lim : IsSuccLimit l
  l_lt : l < E.B
  l_Z : l < evZ gwZ
  EN : E.N = 1
  hN : ∀ μ, μ < l → (F μ).N = 1
  ix : ∀ μ, μ < l → (F μ).ix = gwZ + μ
  γ0 : (F 0).γ = 0
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (evZ (lgG x) + E.R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ E.g μ < x)

namespace GwYFam

variable (Q : GwYFam)

theorem l_pos : 0 < Q.l := Q.l_lim.bot_lt

theorem B_eq {ν : Ordinal.{0}} (h : ν < Q.l) : (Q.F ν).B = veblen 1 (gwZ + ν) := by
  rw [(Q.F ν).B_ix, Q.ix ν h]

theorem B_lt {ν : Ordinal.{0}} (h : ν < Q.l) : (Q.F ν).B < veblen 1 (gwZ + Q.l) := by
  rw [Q.B_eq h]
  exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 h)

theorem B_cof {c : Ordinal.{0}} (hc : c < veblen 1 (gwZ + Q.l)) : ∃ ν, ν < Q.l ∧ c < (Q.F ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.l_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff Q.l_pos.ne').1 ht
  exact ⟨d, hd, by rw [Q.B_eq hd]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

/-- The first member containing `c`. -/
noncomputable def N (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < Q.l ∧ c < (Q.F ν).B}

theorem N_spec {c ν : Ordinal.{0}} (hν : ν < Q.l) (hc : c < (Q.F ν).B) :
    Q.N c ≤ ν ∧ Q.N c < Q.l ∧ c < (Q.F (Q.N c)).B := by
  have hne : ({ν | ν < Q.l ∧ c < (Q.F ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem N_min {c μ : Ordinal.{0}} (hμ : μ < Q.N c) (hμl : μ < Q.l) : ¬ c < (Q.F μ).B := fun hcμ =>
  absurd (csInf_le' ⟨hμl, hcμ⟩ : Q.N c ≤ μ) (not_le.2 hμ)

theorem N_high {c : Ordinal.{0}} (hc : veblen 1 (gwZ + Q.l) ≤ c) : Q.N c = 0 := by
  unfold GwYFam.N
  have he : ({ν | ν < Q.l ∧ c < (Q.F ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd ((hcν.trans (Q.B_lt hν))) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (Q.F (Q.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (Q.F (Q.N c)).g c

theorem R_eq {c ν : Ordinal.{0}} (hν : ν < Q.l) (hc : c < (Q.F ν).B) (x : Ordinal.{0}) :
    Q.R c x = (Q.F ν).R c x := by
  obtain ⟨h1, -, h3⟩ := Q.N_spec hν hc
  exact (Q.cohR _ _ h1 hν c x h3).symm

theorem g_eq {c ν : Ordinal.{0}} (hν : ν < Q.l) (hc : c < (Q.F ν).B) : Q.g c = (Q.F ν).g c := by
  obtain ⟨h1, -, h3⟩ := Q.N_spec hν hc
  exact (Q.cohg _ _ h1 hν c h3).symm

theorem lim' : IsSuccLimit (veblen 1 (gwZ + Q.l)) := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

theorem R_succ' (c x : Ordinal.{0}) : Q.R (c + 1) x = Q.R c x + 1 := by
  rcases lt_or_ge c (veblen 1 (gwZ + Q.l)) with h | h
  · obtain ⟨n, hn1, hn⟩ := Q.B_cof (Q.lim'.add_one_lt h)
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 ((lt_add_one c).trans hn), (Q.F n).R_succ]
  · unfold GwYFam.R
    rw [Q.N_high h, Q.N_high (h.trans (le_self_add (a := c) (b := 1))), (Q.F 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : Q.g c ≤ Q.g (c + 1) := by
  rcases lt_or_ge c (veblen 1 (gwZ + Q.l)) with h | h
  · obtain ⟨n, hn1, hn⟩ := Q.B_cof (Q.lim'.add_one_lt h)
    rw [Q.g_eq hn1 hn, Q.g_eq hn1 ((lt_add_one c).trans hn)]; exact (Q.F n).g_le_succ c
  · unfold GwYFam.g
    rw [Q.N_high h, Q.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (Q.F 0).g_le_succ c

/-- **A code of the union with gate below an `ε`-number `σ` lies in a member with gate below `σ`.** -/
theorem small' {c σ : Ordinal.{0}} (hc : c < veblen 1 (gwZ + Q.l)) (hσ : InE σ) (hg : Q.g c < σ) :
    ∃ μ, μ < Q.l ∧ c < (Q.F μ).B ∧ (Q.F μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
  obtain ⟨-, hN1, hcN⟩ := Q.N_spec hn1 hn
  have hgN : Q.g c = (Q.F (Q.N c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (Q.N c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨Q.N c, hN1, hcN, ?_⟩
    rw [h0, Q.γ0]; exact hσ.pos
  · have hm' : Q.N c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < Q.N c := by rw [hm']; exact lt_add_one m
    have hml : m < Q.l := hmN.trans hN1
    have hBc : (Q.F m).B ≤ c := not_lt.1 (Q.N_min hmN hml)
    have hs : Q.F (Q.N c) = (Q.F m).step := by rw [hm']; exact Q.succ m (hm' ▸ hN1)
    refine ⟨Q.N c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((Q.F m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [Q.B_eq hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < Q.l := hd.trans hN1
    refine Q.N_min hd hdl ?_
    rw [Q.B_eq hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

theorem b_le {μ x : Ordinal.{0}} (hμ : μ < Q.l) (hx : InE x) (hx1 : x < Om1) (hγx : Q.E.g Q.l < x)
    (hμx : (Q.F μ).γ < x) : (Q.F μ).b x ≤ veblen 1 (evZ (lgG x) + Q.E.R Q.l x) := by
  rw [Q.hb μ hμ x hx hx1 hμx]
  refine (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 ?_)
  exact (Q.E.mono x hx hx1 Q.l Q.l_lt μ hμ hγx ((Q.hγ μ hμ x hx hx1).1 hμx)).le

theorem l_omega {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : Q.E.g Q.l < x) : ω ≤ Q.E.R Q.l x :=
  Q.E.R_omega x hx hx1 Q.l (omega0_le_of_isSuccLimit Q.l_lim) Q.l_lt hγx

theorem l_RZ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : Q.E.g Q.l < x) :
    Q.E.R Q.l x < evZ (evZ (lgG x)) := by
  have h := Q.E.R_lt_Z x hx hx1 Q.l Q.l_lt hγx
  rw [Q.EN] at h; exact h

/-- The reading of a limit index is a limit. -/
theorem l_read_lim {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : Q.E.g Q.l < x) :
    IsSuccLimit (Q.E.R Q.l x) := by
  obtain ⟨cp, lp, T, -, -, hdec, -⟩ := Q.E.ld Q.l Q.l_lim Q.l_lt
  obtain ⟨e, -, hT, -⟩ := hdec x hx hx1 hγx
  rw [e]
  exact isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hT)

theorem G_lt_B : gcG 0 < veblen 1 (gwZ + Q.l) :=
  (gw_G_lt_Z.trans (lt_add_of_pos_right _ Q.l_pos)).trans_le (right_le_veblen 1 _)

/-- **THE UNION**: bound `φ(1, ζ_{G+1} + λ)`, base gate `g_E(λ)`, base reading `φ(1, ζ_{Γ_{x+1}+1} + λ_E(x))`. -/
noncomputable def U : GwZD where
  N := 1
  B := veblen 1 (gwZ + Q.l)
  γ := Q.E.g Q.l
  γ_lt := Q.E.g_lt Q.l Q.l_lt
  γ_cl := fun _ hZ hZ1 h => gwY_cl_gate Q.E Q.l_lt Q.l_pos Q.l_Z hZ hZ1 h
  γ_G := fun h => absurd h Q.G_lt_B.ne'
  R := Q.R
  g := Q.g
  b := fun x => veblen 1 (evZ (lgG x) + Q.E.R Q.l x)
  ba := fun x => evZ (lgG x) + (Q.E.R Q.l x + 1)
  ix := gwZ + Q.l
  B_E := omega0_opow_epsilon _
  G_le := Q.G_lt_B.le
  B_lt1 := gwY_veb_lt1 Q.l_Z
  B_ix := rfl
  ix_mem := fun S a b ha hb => CSet.add_mem (gwZ_mem S ha) (Q.E.mem S a b ha Q.l Q.l_lt hb).1
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.g_eq hn1 hn]; exact (Q.F n).g_lt c hn
  g_zero := by rw [Q.g_eq Q.l_pos (Q.F 0).B_pos]; exact (Q.F 0).g_zero
  g_nat := fun k => by rw [Q.g_eq Q.l_pos ((Q.F 0).nat_lt_B k)]; exact (Q.F 0).g_nat k
  g_E := by rw [Q.g_eq Q.l_pos (Q.F 0).E_lt_B]; exact (Q.F 0).g_E
  g_lowE := fun c hc => by rw [Q.g_eq Q.l_pos (hc.trans (Q.F 0).E_lt_B)]; exact (Q.F 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof h
    rw [Q.g_eq hn1 hn]; exact (Q.F n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hxy
    have hx : x < (Q.F n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (Q.F n).B := lt_of_le_of_lt le_add_self hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hx] at hgx; rw [Q.g_eq hn1 hy] at hgy
    exact (Q.F n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hy
    have hy' : y < (Q.F n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hy'] at hg
    exact (Q.F n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hcB
    rw [Q.g_eq hn1 hn]
    exact (Q.F n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (Q.B_lt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    have hc' : c < (Q.F n).B := (lt_add_one c).trans hn
    rw [Q.g_eq hn1 hn]; rw [Q.g_eq hn1 hc'] at hg
    exact (Q.F n).g_succ Z hZ c hn hg
  g_le_succ := Q.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).mem S a b ha c hn hg
  R_zero := fun x => by rw [Q.R_eq Q.l_pos (Q.F 0).B_pos]; exact (Q.F 0).R_zero x
  R_nat := fun k x => by rw [Q.R_eq Q.l_pos ((Q.F 0).nat_lt_B k)]; exact (Q.F 0).R_nat k x
  R_E := fun x => by rw [Q.R_eq Q.l_pos (Q.F 0).E_lt_B]; exact (Q.F 0).R_E x
  R_succ := Q.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := Q.small' hc hx hg
    rw [Q.R_eq hμ hcμ]; rw [Q.g_eq hμ hcμ] at hg
    exact ((Q.F μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans_le (Q.b_le hμ hx hx1 hγx hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    have h := (Q.F n).R_lt_Z x hx hx1 c hn hg
    rw [Q.hN n hn1] at h; exact h
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    have hd : d < (Q.F n).B := hdc.trans hn
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hd]; rw [Q.g_eq hn1 hn] at hgc; rw [Q.g_eq hn1 hd] at hgd
    exact (Q.F n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn] at hν; rw [Q.g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (Q.F n).cof x hx hx1 c hn hg ν hν
    have hd : d < (Q.F n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [Q.g_eq hn1 hd]; exact hgd, by rw [Q.R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
    have hRl := Q.l_read_lim hx hx1 hγx
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hRl)).1 hν
    obtain ⟨d0, hd0, htd⟩ := (lt_add_iff hRl.bot_lt.ne').1 ht
    obtain ⟨e, hel, hge, hd0e⟩ := Q.E.cof x hx hx1 Q.l Q.l_lt hγx d0 hd0
    have he1 : e + 1 < Q.l := Q.l_lim.add_one_lt hel
    have hge1 : Q.E.g (e + 1) < x := Q.E.g_succ x hxl e (he1.trans Q.l_lt) hge
    have hγe1 : (Q.F (e + 1)).γ < x := (Q.hγ (e + 1) he1 x hx hx1).2 hge1
    have hνb : ν < (Q.F (e + 1)).b x := by
      rw [Q.hb (e + 1) he1 x hx hx1 hγe1, Q.E.R_succ]
      refine hνt.trans_le ((isNormal_veblen 1).monotone (htd.trans ?_))
      exact (add_le_add_iff_left _).2 (hd0e.trans (le_self_add))
    obtain ⟨d, hd, hgd, hνd⟩ := (Q.F (e + 1)).b_cof x hx hx1 hγe1 ν hνb
    exact ⟨d, hd.trans (Q.B_lt he1), by rw [Q.g_eq he1 hd]; exact hgd, by rw [Q.R_eq he1 hd]; exact hνd⟩
  b_E := fun _ _ _ _ => omega0_opow_epsilon _
  x_lt_b := fun x hx hx1 _ =>
    ((lgG_facts hx hx1).2.1.trans (lt_evZ _)).trans_le (le_self_add.trans (right_le_veblen 1 _))
  b_eN := fun x hx hx1 hγx => gw_b_eN_Z hx hx1 (Q.l_omega hx hx1 hγx) (Q.l_RZ hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => (add_lt_evZ (lt_evZ _) ((ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt
    (Q.l_RZ hx hx1 hγx))).trans (gw_evZ_lt1 hx hx1 (gn_evZG_lt1 hx hx1))
  b_Z := fun x hx hx1 hγx => by
    show _ < evZ (evZ (lgG x))
    refine go_eN_lt_evZ ?_
    have := (isNormal_veblen 1).strictMono (add_lt_evZ (lt_evZ (evZ (lgG x))) (Q.l_RZ hx hx1 hγx))
    rwa [show veblen 1 (evZ (evZ (lgG x))) = evZ (evZ (lgG x)) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB hγσ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.E.g Q.l < ρ := hγσ.trans hB.2.2.1
    obtain ⟨e1, e2⟩ := Q.E.ex σ ρ hB Q.l Q.l_lt hγσ
    exact gw_b_pi_Z hB e1 (Q.l_RZ hB.2.1 hρ1 hγρ) (Q.l_RZ hB.1 hσ1 hγσ) (Q.l_omega hB.2.1 hρ1 hγρ) e2
  ba_pi := fun σ ρ hB hγσ => by
    obtain ⟨z1, z2⟩ := gw_Z_pi hB
    obtain ⟨e1, e2⟩ := Q.E.ex σ ρ hB Q.l Q.l_lt hγσ
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨s1, s2⟩ := pi_add hB e1 o1
    obtain ⟨t1, t2⟩ := pi_add hB z1 s1
    exact ⟨t1, by rw [t2, s2, z2, e2, o2]⟩
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hn]; rw [Q.g_eq hn1 hn] at hg
    exact (Q.F n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := Q.small' hd hB.1 hg
    rw [Q.R_eq hμ hdμ, Q.R_eq hμ hdμ]; rw [Q.g_eq hμ hdμ] at hg
    exact (Q.F μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (Q.b_le hμ hB.2.1 hB.2.2.2 (hγσ.trans hB.2.2.1) (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := Q.B_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (Q.F n).ld c hl hn
    have hcpn : cp < (Q.F n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [Q.g_eq hn1 hn, Q.g_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← Q.g_eq hn1 hn]; exact hg)⟩
    rw [Q.g_eq hn1 hn] at hg
    rw [Q.R_eq hn1 hn, Q.R_eq hn1 hcpn]
    exact hdec x hx hx1 hg

theorem U_B : Q.U.B = veblen 1 (gwZ + Q.l) := rfl

theorem U_γ : Q.U.γ = Q.E.g Q.l := rfl

theorem U_N : Q.U.N = 1 := rfl

theorem U_ix : Q.U.ix = gwZ + Q.l := rfl

theorem U_b (x : Ordinal.{0}) : Q.U.b x = veblen 1 (evZ (lgG x) + Q.E.R Q.l x) := rfl

theorem U_ba (x : Ordinal.{0}) : Q.U.ba x = evZ (lgG x) + (Q.E.R Q.l x + 1) := rfl

/-- **The union extends every member** (readings). -/
theorem U_R {ν c : Ordinal.{0}} (hν : ν < Q.l) (hc : c < (Q.F ν).B) (x : Ordinal.{0}) : Q.U.R c x = (Q.F ν).R c x :=
  Q.R_eq hν hc x

/-- **The union extends every member** (gates). -/
theorem U_g {ν c : Ordinal.{0}} (hν : ν < Q.l) (hc : c < (Q.F ν).B) : Q.U.g c = (Q.F ν).g c := Q.g_eq hν hc

end GwYFam

end Googology.Trans.PoR.InaccPsi.R2.Gw
