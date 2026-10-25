import Googology.Trans.PoR.InaccPsi.R2.GzVRS

/-!
# THE BASE DATA AT ANY `ε`-FIXED PSEUDO-BASE BELOW `B₃(x)`, AND THE PARAMETERS OF A STAGE

`R2.GzZb` proves the base data at the pseudo-bases `Z_n(x) = ζ_{Γ_{x+1}+n}` by induction on `n`.  Here they hold at
EVERY `ε`-fixed point `P ∈ (x, Γ_{x+2})` directly:

* `gz_LuP2_of_fix`, `gz_low_fix` (**`ϑˣ(Ω₁ + σ) < P` for `σ < P`**: `≤` by `Gl.glA_min`, `≠` because `ϑˣ(Ω₁ + σ)` is
  not an `ε`-fixed point, `Gl.glA_notP`), `gz_eN_fix` (**`ε_{P+1} = ϑˣ(Ω₁ + P)`**), `gz_evIx_fix`, `gz_glAP`
  (**`ϑˣ(Ω₁ + P + ν) = ε_{P+1+ν}`, `ν < evZ(P)`**), `gz_bP_eN`, `gz_bP_pi` (**Lemma EXACT for `φ(1, P(ρ) + ν(ρ))`**),
  `gz_evZ_lt_B3`;
* `GzPB` (**the parameters of a stage**: the index base `Q = φ(2, j_Q)` (a `ζ`-point `≥ ζ_{G+1}`), its reading
  `P(x) = ϑˣ(Ω₁·2 + t_P(x))` with `t_P` EXACT, and `P(x) < B₃(x)`), `GzPB.Q`, `GzPB.P` and their facts (`Q_fix`,
  `Q_mem`, `Q_cl`, `evQ`, `evQ_lt1`, `P_T`, `P_gt`, `P_fix`, `P_lt`, `evP`, `P_pi`, `evP_pi`, `evP_B3`);
* the generic index facts above `Q` (`gzq_lt_veb`, `gzq_self_lt`, `gzq_veb_lt_Z`, `gzq_cover`, `gzq_cl_gate`).

No new axiom.  New definitions: `GzPB`, `GzPB.Q`, `GzPB.P`.
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

/-! ## `ε`-fixed points -/

theorem gz_LuP2_of_fix {P : Ordinal.{0}} (hP : veblen 1 P = P) : LuP 2 P := by
  unfold LuP
  rw [mem_range_veblen two_ne_zero]
  intro b hb
  rcases lt_or_ge b 1 with h0 | h1
  · rw [Order.lt_one_iff] at h0
    rw [h0, veblen_zero_apply]; exact gz_inE_of_fix hP
  · have hb1 : b = 1 := le_antisymm (Order.lt_add_one_iff.1 (by rw [one_add_one_eq_two]; exact hb)) h1
    rw [hb1]; exact hP

theorem gz_evIx_fix {P : Ordinal.{0}} (hP : veblen 1 P = P) : evIx P = P := by
  have h1 : Ordinal.epsilon (evIx P) = P := epsilon_evIx (gz_inE_of_fix hP)
  exact (veblen_inj).1 (h1.trans hP.symm)

theorem gz_veb_fix (P ν : Ordinal.{0}) (hP : veblen 1 P = P) : veblen 1 (P + ν) = evA P ν := by
  show veblen 1 _ = Ordinal.epsilon (evIx P + ν)
  rw [gz_evIx_fix hP]

/-- **`evZ(u) < B₃(x)` for `u < B₃(x)`.** -/
theorem gz_evZ_lt_B3 {u x : Ordinal.{0}} (hu : u < gzB3 x) : evZ u < gzB3 x := by
  have h3 : evZ u ≤ veblen 2 (u + 1) :=
    evZ_le ((lt_add_one u).trans_le (right_le_veblen 2 _)) (veblen_veblen_of_lt one_lt_two _)
  have h4 := (isNormal_veblen 2).strictMono ((ev_isSuccLimit_of_inE (gzB3_E x)).add_one_lt hu)
  rw [gzB3_fix] at h4
  exact h3.trans_lt h4

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁ + σ) < P` for every `σ < P`**, `P ∈ (x, Γ_{x+2})` an `ε`-fixed point. -/
theorem gz_low_fix {P : Ordinal.{0}} (hP : veblen 1 P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    ∀ σ, σ < P → glA 1 σ x < P := by
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hPE : InE P := gz_inE_of_fix hP
  have hP2 : LuP (1 + 1) P := by rw [one_add_one_eq_two]; exact gz_LuP2_of_fix hP
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσ.trans hPq)
  have hle : glA 1 σ x ≤ P := glA_min hx hx1 le_rfl h1T h11 hσT hσ1 ⟨P, hP⟩ hxP hσ (lu_one_lt_E hPE)
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 le_rfl h1T h11 hσT hσ1 (by rw [e]; exact hP2))

/-- **`ε_{P+1} = ϑˣ(Ω₁ + P)`** at every `ε`-fixed point `P ∈ (x, Γ_{x+2})`. -/
theorem gz_eN_fix {P : Ordinal.{0}} (hP : veblen 1 P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    eN P = glA 1 P x :=
  gz_eN_of_low hx hx1 (gz_inE_of_fix hP) hxP hPq (gz_low_fix hx hx1 hP hxP hPq)

/-- **`ϑˣ(Ω₁ + P + ν) = ε_{P+1+ν}`** for `ν < evZ(P)`. -/
theorem gz_glAP {P ν : Ordinal.{0}} (hP : veblen 1 P = P) (hxP : x < P) (hPq : P < gq 1 x) (hν : ν < evZ P) :
    glA 1 (P + ν) x = evA P (1 + ν) := by
  have hPE := gz_inE_of_fix hP
  have hq : P + ν < gq 1 x := (add_lt_evZ (lt_evZ _) hν).trans (gw_evZ_lt1 hx hx1 hPq)
  exact gw_glA_eqP hx hx1 hPE hxP (gz_eN_fix hx hx1 hP hxP hPq).symm (gz_low_fix hx hx1 hP hxP hPq) ν hq
    (fun ν' h _ => gw_lt_evA hPE (lt_of_le_of_lt h hν))

/-- **`ε_{b+1} = ϑˣ(Ω₁ + P + ν + 1)` for `b = φ(1, P + ν)`** (`ω ≤ ν < evZ(P)`). -/
theorem gz_bP_eN {P ν : Ordinal.{0}} (hP : veblen 1 P = P) (hxP : x < P) (hPq : P < gq 1 x) (hω : ω ≤ ν)
    (hν : ν < evZ P) : eN (veblen 1 (P + ν)) = glA 1 (P + (ν + 1)) x := by
  have hν1 : ν + 1 < evZ P := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt hν
  rw [gz_glAP hx hx1 hP hxP hPq hν1, one_add_of_omega0_le (hω.trans le_self_add), go_eN_veb, add_assoc]
  exact gz_veb_fix _ _ hP

end Base

/-- **Lemma EXACT for `φ(1, P(ρ) + ν(ρ))`** at an `ε`-fixed pseudo-base `P` with `π(P(ρ)) = P(σ)`
(`ω ≤ ν(ρ) < evZ(P(ρ))`, `π(ν(ρ)) = ν(σ) < evZ(P(σ))`). -/
theorem gz_bP_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) {P : Ordinal.{0} → Ordinal.{0}}
    (hPρ : veblen 1 (P ρ) = P ρ) (hPσ : veblen 1 (P σ) = P σ) (hxPρ : ρ < P ρ) (hxPσ : σ < P σ)
    (hPqρ : P ρ < gq 1 ρ) (hPqσ : P σ < gq 1 σ) (hPpi : P ρ ∈ TB ρ σ ∧ pi σ ρ (P ρ) = P σ)
    {ν ν' : Ordinal.{0}} (hνT : ν ∈ TB ρ σ) (hν : ν < evZ (P ρ)) (hν' : ν' < evZ (P σ)) (hω : ω ≤ ν)
    (hπ : pi σ ρ ν = ν') :
    veblen 1 (P ρ + ν) ∈ TB ρ σ ∧ pi σ ρ (veblen 1 (P ρ + ν)) = veblen 1 (P σ + ν') := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨z1, z2⟩ := hPpi
  obtain ⟨s1, s2⟩ := pi_add hB z1 hνT
  rw [z2, hπ] at s2
  have hq : P ρ + ν < gq 1 ρ := (add_lt_evZ (lt_evZ _) hν).trans (gw_evZ_lt1 hB.2.1 hρ1 hPqρ)
  have hs1 : P ρ + ν < Om1 := (gm1_T hB.2.1 hρ1 hq).2
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 hs1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωT : ω ∈ TB ρ σ := mem_TB_of_lt hB hωσ
  have hω' : ω ≤ ν' := by
    rw [← hπ, ← pi_lt hB hωσ]
    exact ((pi_bijOn hB).2.le_iff_le hωT hνT).2 hω
  rw [o2, s2, gz_glAP hB.2.1 hρ1 hPρ hxPρ hPqρ hν, gz_glAP hB.1 hσ1 hPσ hxPσ hPqσ hν',
    one_add_of_omega0_le hω, one_add_of_omega0_le hω'] at h
  rw [gz_veb_fix _ _ hPρ, gz_veb_fix _ _ hPσ]
  exact h

/-! ## Indices above an `ε`-fixed point `Q ≥ G` -/

section Idx

variable {Q : Ordinal.{0}} (hQ : veblen 1 Q = Q)
include hQ

theorem gzq_lt_veb {d : Ordinal.{0}} (hd0 : 0 < d) (hd : d < evZ Q) : Q + d < veblen 1 (Q + d) := by
  rcases (right_le_veblen 1 (Q + d)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : Ordinal.epsilon (Q + d) = Q + d := h.symm
    have h1 := evZ_le (lt_add_of_pos_right Q hd0) hfix
    exact absurd (add_lt_evZ (lt_evZ Q) hd) (not_lt.2 h1)

theorem gzq_self_lt {d : Ordinal.{0}} (hd : d < evZ Q) : d < veblen 1 (Q + d) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero, hQ]; exact (gz_inE_of_fix hQ).pos
  · exact (le_add_self : d ≤ Q + d).trans_lt (gzq_lt_veb hQ (pos_iff_ne_zero.2 hd0) hd)

omit hQ in
theorem gzq_veb_lt_Z {d : Ordinal.{0}} (hd : d < evZ Q) : veblen 1 (Q + d) < evZ Q := by
  have := (isNormal_veblen 1).strictMono (add_lt_evZ (lt_evZ Q) hd)
  rwa [show veblen 1 (evZ Q) = evZ Q from epsilon_evZ _] at this

theorem gzq_cover {μ : Ordinal.{0}} (hμ0 : 0 < μ) (hμ : μ < evZ Q) : ∃ d, d < μ ∧ μ < veblen 1 (Q + d) := by
  rcases zero_or_succ_or_isSuccLimit μ with h0 | ⟨d, hd⟩ | hlim
  · exact absurd h0 hμ0.ne'
  · have hd' : μ = d + 1 := by rw [← hd, Order.succ_eq_add_one]
    have hdμ : d < μ := by rw [hd']; exact lt_add_one d
    refine ⟨d, hdμ, ?_⟩
    rw [hd']
    exact (ev_isSuccLimit_of_inE (omega0_opow_epsilon _)).add_one_lt (gzq_self_lt hQ (hdμ.trans hμ))
  · have h := gzq_self_lt hQ hμ
    obtain ⟨t, ht, hμt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 h
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    exact ⟨d, hd, hμt.trans_le ((isNormal_veblen 1).monotone htd)⟩

/-- **THE CODE-GATE CONDITION OF AN INDEX ABOVE `Q`**: `φ(1, Q + c)` a code over a strongly critical `Z ≤ Ω₁`, `Q`
a code over `Z`, `G ≤ Q`, and `c` (`0 < c < evZ(Q)`) a code of `E` ⇒ `g_E(c) < Z`. -/
theorem gzq_cl_gate (hGQ : gcG 0 ≤ Q) (E : GzVD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c)
    (hcZ : c < evZ Q) (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hQcl : GxCl Z {gcG 0} Q)
    (h : GxCl Z {gcG 0} (veblen 1 (Q + c))) : E.g c < Z := by
  have hOt : Om 1 < Q + c := ((gcG_Om1_lt 0).trans_le hGQ).trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gzq_lt_veb hQ hc0 hcZ) h
  have h2 := gwY_cl_of_add hZ hZ1 (gz_inE_of_fix hQ) hGQ hQcl h1
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

end Idx

/-! ## The parameters of a stage -/

/-- **The parameters of a stage**: the index base `Q = φ(2, j_Q)` and its reading `P(x) = ϑˣ(Ω₁·2 + t_P(x))`. -/
structure GzPB where
  jQ : Ordinal.{0}
  tP : Ordinal.{0} → Ordinal.{0}
  jQ_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → jQ ∈ S.CSet a b
  jQ_cl : ∀ Z : Ordinal.{0}, SC Z → GxCl Z {gcG 0} jQ
  G_lt_Q : gcG 0 < veblen 2 jQ
  Q_lt1 : veblen 2 (jQ + 1) < gcG 1
  tP_lt : ∀ x, InE x → x < Om1 → tP x + 1 < gq 1 x
  tP_pi : ∀ σ ρ, Bases σ ρ → tP ρ ∈ TB ρ σ ∧ pi σ ρ (tP ρ) = tP σ
  P_B3 : ∀ x, InE x → x < Om1 → glA 2 (tP x) x < gzB3 x

namespace GzPB

variable (Bp : GzPB)

/-- The index base `Q = φ(2, j_Q)`. -/
noncomputable def Q : Ordinal.{0} := veblen 2 Bp.jQ

/-- The reading of the index base, `P(x) = ϑˣ(Ω₁·2 + t_P(x))`. -/
noncomputable def P (x : Ordinal.{0}) : Ordinal.{0} := glA 2 (Bp.tP x) x

theorem Q_fix : veblen 1 Bp.Q = Bp.Q := veblen_veblen_of_lt one_lt_two _

theorem Q_E : InE Bp.Q := gz_inE_of_fix Bp.Q_fix

theorem G_le_Q : gcG 0 ≤ Bp.Q := Bp.G_lt_Q.le

theorem Q_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : Bp.Q ∈ S.CSet a b :=
  CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1))) (Bp.jQ_mem S a b ha)

theorem Q_cl {Z : Ordinal.{0}} (hZ : SC Z) : GxCl Z {gcG 0} Bp.Q :=
  GxCl.phi (GxCl.small (gw_two_lt_w.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ)))) (Bp.jQ_cl Z hZ)

theorem evQ : evZ Bp.Q = veblen 2 (Bp.jQ + 1) := gz_evZ_veb2 _

theorem evQ_lt1 : evZ Bp.Q < gcG 1 := by rw [Bp.evQ]; exact Bp.Q_lt1

theorem evQ_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : evZ Bp.Q ∈ S.CSet a b := by
  rw [Bp.evQ]
  exact CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1)))
    (CSet.succ_mem (Bp.jQ_mem S a b ha))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem tP_T : Bp.tP x ∈ Tset x ∧ Bp.tP x < Om1 := gm1_T hx hx1 ((lt_add_one _).trans (Bp.tP_lt x hx hx1))

theorem P_facts : Bp.P x ∈ Tset x ∧ x < Bp.P x ∧ Bp.P x < Om1 ∧ InE (Bp.P x) := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  obtain ⟨hT, h1⟩ := Bp.tP_T hx hx1
  obtain ⟨a1, a2, a3, a4, -, -⟩ := glA_facts hx hx1 one_le_two h2T h21 hT h1
  exact ⟨a1, a2, a3, a4⟩

theorem P_gt : x < Bp.P x := (Bp.P_facts hx hx1).2.1

theorem P_fix : veblen 1 (Bp.P x) = Bp.P x := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  obtain ⟨hT, h1⟩ := Bp.tP_T hx hx1
  obtain ⟨k, hk⟩ := glA_P hx hx1 one_le_two h2T h21 hT h1
  show veblen 1 (glA 2 _ x) = glA 2 _ x
  rw [← hk]; exact veblen_veblen_of_lt one_lt_two k

theorem P_lt : Bp.P x < gq 1 x := (Bp.P_B3 x hx hx1).trans (gzB3_lt1 hx hx1)

theorem P_lt_B3 : Bp.P x < gzB3 x := Bp.P_B3 x hx hx1

/-- **`evZ(P(x)) = ϑˣ(Ω₁·2 + t_P(x) + 1)`.** -/
theorem evP : evZ (Bp.P x) = glA 2 (Bp.tP x + 1) x := (gz_glA2_succ hx hx1 (Bp.tP_lt x hx hx1)).symm

theorem evP_B3 : evZ (Bp.P x) < gzB3 x := gz_evZ_lt_B3 (Bp.P_B3 x hx hx1)

theorem evP_lt : evZ (Bp.P x) < gq 1 x := (Bp.evP_B3 hx hx1).trans (gzB3_lt1 hx hx1)

theorem evP_gt : x < evZ (Bp.P x) := (Bp.P_gt hx hx1).trans (lt_evZ _)

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **Lemma EXACT for `P(ρ)`.** -/
theorem P_pi : Bp.P ρ ∈ TB ρ σ ∧ pi σ ρ (Bp.P ρ) = Bp.P σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have h2σ : (2 : Ordinal.{0}) < σ :=
    (show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hB.1)
  obtain ⟨t1, t2⟩ := Bp.tP_pi σ ρ hB
  have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 t1 (Bp.tP_T hB.2.1 hρ1).2
  rw [pi_lt hB h2σ, t2] at h
  exact h

/-- **Lemma EXACT for `evZ(P(ρ))`.** -/
theorem evP_pi : evZ (Bp.P ρ) ∈ TB ρ σ ∧ pi σ ρ (evZ (Bp.P ρ)) = evZ (Bp.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have h2σ : (2 : Ordinal.{0}) < σ :=
    (show (2 : Ordinal.{0}) < ω from nat_lt_omega0 2).trans (omega0_lt_inE hB.1)
  obtain ⟨t1, t2⟩ := Bp.tP_pi σ ρ hB
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB t1 o1
  rw [t2, o2] at s2
  have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 s1
    (gm1_T hB.2.1 hρ1 (Bp.tP_lt ρ hB.2.1 hρ1)).2
  rw [pi_lt hB h2σ, s2, ← Bp.evP hB.2.1 hρ1, ← Bp.evP hB.1 hσ1] at h
  exact h

end Pi

end GzPB

end Googology.Trans.PoR.InaccPsi.R2.Gz
