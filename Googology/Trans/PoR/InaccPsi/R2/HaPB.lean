import Googology.Trans.PoR.InaccPsi.R2.HaCl

/-!
# HaPB: A STAGE WITH A GATED `ζ`-INDEX

`Gz.GzPB` asks Lemma EXACT for the reading `t_P` of the index at EVERY pair of bases, so the `ζ`-index of a stage must
be a constant below every base (`Gz.gz_wall_e0`).  `HaPB` is `Gz.GzPB` with a stage gate `γ_P`: membership of `j_Q`
in the hulls, Lemma EXACT for `t_P` and the bounds on `P(x)` are asked only above `γ_P`; in place of "`j_Q` is a code
over every `Z`" it asks the code-gate condition "a code in `[Q, evZ(Q))` over `Z` forces `γ_P < Z`".  The bound field
of the stage is `Zst(x) = evZ(P(x))` above the gate and `B₃(x)` below it.

* `HaPB`, `HaPB.Q`, `HaPB.P`, `HaPB.Zst` and their facts (all above the gate);
* `HaPB.strip` (**`φ(1, Q + c)` a code over `Z` ⇒ `γ_P < Z` and `c` a code over `Z`**), `HaPB.cl_gate` (the gate
  condition of the union index `Q + c`);
* `haPBof E λ` (**THE STAGE AT A ζ-INDEX `λ` READ BY A SYSTEM `E`**: `Q = φ(2, G + 1 + λ)`, `t_P(x) = Γ_{x+1} + λ(x)`,
  gate `g_E(λ)`), `haPBof_P` (**`P(x) = φ(2, i₀(x) + λ(x))`**).

No new axiom.  New definitions: `HaPB`, `HaPB.Q`, `HaPB.P`, `HaPB.Zst`, `haPBof`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A stage with a gated `ζ`-index**: the index base `Q = φ(2, j_Q)`, its reading `P(x) = ϑˣ(Ω₁·2 + t_P(x))` above
the stage gate `γ_P`. -/
structure HaPB where
  jQ : Ordinal.{0}
  tP : Ordinal.{0} → Ordinal.{0}
  γP : Ordinal.{0}
  γP_lt : γP < Om1
  jQ_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → γP < b → jQ ∈ S.CSet a b
  jQ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z {gcG 0} y → veblen 2 jQ ≤ y →
    y < evZ (veblen 2 jQ) → γP < Z
  jQ_lt : jQ < veblen 2 jQ
  G_lt_Q : gcG 0 < veblen 2 jQ
  Q_lt1 : veblen 2 (jQ + 1) < gcG 1
  tP_lt : ∀ x, InE x → x < Om1 → γP < x → tP x + 1 < gq 1 x
  tP_pi : ∀ σ ρ, Bases σ ρ → γP < σ → tP ρ ∈ TB ρ σ ∧ pi σ ρ (tP ρ) = tP σ
  P_B3 : ∀ x, InE x → x < Om1 → γP < x → glA 2 (tP x) x < gzB3 x

namespace HaPB

variable (Bp : HaPB)

/-- The index base `Q = φ(2, j_Q)`. -/
noncomputable def Q : Ordinal.{0} := veblen 2 Bp.jQ

/-- The reading of the index base, `P(x) = ϑˣ(Ω₁·2 + t_P(x))`. -/
noncomputable def P (x : Ordinal.{0}) : Ordinal.{0} := glA 2 (Bp.tP x) x

open Classical in
/-- **The bound field of the stage**: `evZ(P(x))` above the gate, `B₃(x)` at or below it. -/
noncomputable def Zst (x : Ordinal.{0}) : Ordinal.{0} := if Bp.γP < x then evZ (Bp.P x) else gzB3 x

theorem Q_fix : veblen 1 Bp.Q = Bp.Q := veblen_veblen_of_lt one_lt_two _

theorem Q_E : InE Bp.Q := gz_inE_of_fix Bp.Q_fix

theorem G_le_Q : gcG 0 ≤ Bp.Q := Bp.G_lt_Q.le

theorem Om_lt_Q : Om 1 < Bp.Q := (gcG_Om1_lt 0).trans Bp.G_lt_Q

theorem Q_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : Bp.γP < b) : Bp.Q ∈ S.CSet a b :=
  CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1))) (Bp.jQ_mem S a b ha hb)

theorem evQ : evZ Bp.Q = veblen 2 (Bp.jQ + 1) := gz_evZ_veb2 _

theorem evQ_lt1 : evZ Bp.Q < gcG 1 := by rw [Bp.evQ]; exact Bp.Q_lt1

theorem Q_lt_G1 : Bp.Q < gcG 1 := (lt_evZ _).trans Bp.evQ_lt1

theorem evQ_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) (hb : Bp.γP < b) : evZ Bp.Q ∈ S.CSet a b := by
  rw [Bp.evQ]
  exact CSet.phi_mem (gr_cst_mem ha b 2 (gw_two_lt_w.trans (omega0_lt_gamma 1)))
    (CSet.succ_mem (Bp.jQ_mem S a b ha hb))

/-- **`Q` is a code over `Z` when a code in `[Q, evZ(Q))` is.** -/
theorem Q_cl {Z y : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hy : GxCl Z {gcG 0} y) (hQy : Bp.Q ≤ y)
    (hyZ : y < evZ Bp.Q) : GxCl Z {gcG 0} Bp.Q :=
  GxCl.phi (GxCl.small (gw_two_lt_w.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hZ))))
    (ha_cl_zj hZ1 Bp.jQ_lt Bp.G_lt_Q hy hQy hyZ)

/-- **`φ(1, Q + c)` a code over `Z` (`0 < c < evZ(Q)`) ⇒ the stage gate lies below `Z` and `c` is a code over
`Z`.** -/
theorem strip {Z c : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (hc0 : 0 < c) (hcZ : c < evZ Bp.Q)
    (h : GxCl Z {gcG 0} (veblen 1 (Bp.Q + c))) : Bp.γP < Z ∧ GxCl Z {gcG 0} c := by
  have hOt : Om 1 < Bp.Q + c := Bp.Om_lt_Q.trans_le le_self_add
  have h1 := gr_cl_veb1 hZ1 hOt (gzq_lt_veb Bp.Q_fix hc0 hcZ) h
  have hy : Bp.Q + c < evZ Bp.Q := add_lt_evZ (lt_evZ _) hcZ
  refine ⟨Bp.jQ_cl Z hZ hZ1 _ h1 le_self_add hy, ?_⟩
  exact gwY_cl_of_add hZ hZ1 Bp.Q_E Bp.G_le_Q (Bp.Q_cl hZ hZ1 h1 le_self_add hy) h1

/-- **THE CODE-GATE CONDITION OF A UNION INDEX `Q + c`**: `φ(1, Q + c)` a code over `Z` ⇒ `max(γ_P, g_E(c)) < Z`. -/
theorem cl_gate (E : GzVD) {c Z : Ordinal.{0}} (hcB : c < E.B) (hc0 : 0 < c) (hcZ : c < evZ Bp.Q) (hZ : SC Z)
    (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (veblen 1 (Bp.Q + c))) : max Bp.γP (E.g c) < Z := by
  obtain ⟨h1, h2⟩ := Bp.strip hZ hZ1 hc0 hcZ h
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  refine max_lt h1 ?_
  exact E.code_gate Z hZ1' hZ.1 (fun _ _ hu hv => hZ.isPrincipal hu hv) (fun _ _ hu hv => hZ.2 _ hu _ hv)
    {gcG 0} (fun s hs => Or.inl (Set.mem_singleton_iff.1 hs)) c h2 hcB

/-- **`evZ(Q)` a code over `Z` ⇒ `γ_P < Z`.** -/
theorem evQ_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} (evZ Bp.Q)) : Bp.γP < Z := by
  have hj1 : Bp.jQ + 1 < veblen 2 (Bp.jQ + 1) :=
    ((ev_isSuccLimit_of_inE Bp.Q_E).add_one_lt Bp.jQ_lt).trans ((isNormal_veblen 2).strictMono (lt_add_one _))
  have hG' : gcG 0 < veblen 2 (Bp.jQ + 1) := Bp.G_lt_Q.trans ((isNormal_veblen 2).strictMono (lt_add_one _))
  rw [Bp.evQ] at h
  have h1 := ha_cl_zj hZ1 hj1 hG' h le_rfl (lt_evZ _)
  have h2 := ha_cl_succ hZ.1 (fun s hs => by rw [Set.mem_singleton_iff.1 hs]; exact ev_isSuccLimit_of_inE gr_G_inE)
    h1 _ rfl
  exact Bp.jQ_cl Z hZ hZ1 Bp.Q (GxCl.phi (GxCl.small (gw_two_lt_w.trans (omega0_lt_inE
    (Low.opow_eq_self_of_SC hZ)))) h2) le_rfl (lt_evZ _)

/-- **`Q` a code over `Z` ⇒ `γ_P < Z`.** -/
theorem Q_gate {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : GxCl Z {gcG 0} Bp.Q) : Bp.γP < Z :=
  Bp.jQ_cl Z hZ hZ1 Bp.Q h le_rfl (lt_evZ _)

theorem Zst_B3 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : Bp.Zst x ≤ gzB3 x := by
  unfold HaPB.Zst
  split_ifs with h
  · exact (gz_evZ_lt_B3 (Bp.P_B3 x hx hx1 h)).le
  · exact le_rfl

theorem Zst_fix (x : Ordinal.{0}) : veblen 1 (Bp.Zst x) = Bp.Zst x := by
  unfold HaPB.Zst
  split_ifs
  · exact epsilon_evZ _
  · have h := veblen_veblen_of_lt (one_lt_two (α := Ordinal.{0})) (gzB3 x)
    rw [gzB3_fix] at h; exact h

theorem Zst_eq {x : Ordinal.{0}} (h : Bp.γP < x) : Bp.Zst x = evZ (Bp.P x) := by
  unfold HaPB.Zst; rw [if_pos h]

theorem Zst_low {x : Ordinal.{0}} (h : ¬ Bp.γP < x) : Bp.Zst x = gzB3 x := by
  unfold HaPB.Zst; rw [if_neg h]

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Bp.γP < x)
include hx hx1 hγ

theorem tP_T : Bp.tP x ∈ Tset x ∧ Bp.tP x < Om1 := gm1_T hx hx1 ((lt_add_one _).trans (Bp.tP_lt x hx hx1 hγ))

theorem P_facts : Bp.P x ∈ Tset x ∧ x < Bp.P x ∧ Bp.P x < Om1 ∧ InE (Bp.P x) := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  obtain ⟨hT, h1⟩ := Bp.tP_T hx hx1 hγ
  obtain ⟨a1, a2, a3, a4, -, -⟩ := glA_facts hx hx1 one_le_two h2T h21 hT h1
  exact ⟨a1, a2, a3, a4⟩

theorem P_gt : x < Bp.P x := (Bp.P_facts hx hx1 hγ).2.1

theorem P_fix : veblen 1 (Bp.P x) = Bp.P x := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  obtain ⟨hT, h1⟩ := Bp.tP_T hx hx1 hγ
  obtain ⟨k, hk⟩ := glA_P hx hx1 one_le_two h2T h21 hT h1
  show veblen 1 (glA 2 _ x) = glA 2 _ x
  rw [← hk]; exact veblen_veblen_of_lt one_lt_two k

theorem P_lt_B3 : Bp.P x < gzB3 x := Bp.P_B3 x hx hx1 hγ

theorem P_lt : Bp.P x < gq 1 x := (Bp.P_lt_B3 hx hx1 hγ).trans (gzB3_lt1 hx hx1)

/-- **`evZ(P(x)) = ϑˣ(Ω₁·2 + t_P(x) + 1)`.** -/
theorem evP : evZ (Bp.P x) = glA 2 (Bp.tP x + 1) x := (gz_glA2_succ hx hx1 (Bp.tP_lt x hx hx1 hγ)).symm

theorem evP_B3 : evZ (Bp.P x) < gzB3 x := gz_evZ_lt_B3 (Bp.P_lt_B3 hx hx1 hγ)

theorem evP_lt : evZ (Bp.P x) < gq 1 x := (Bp.evP_B3 hx hx1 hγ).trans (gzB3_lt1 hx hx1)

theorem evP_gt : x < evZ (Bp.P x) := (Bp.P_gt hx hx1 hγ).trans (lt_evZ _)

end Base

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hγ : Bp.γP < σ)
include hB hγ

/-- **Lemma EXACT for `P(ρ)`** above the stage gate. -/
theorem P_pi : Bp.P ρ ∈ TB ρ σ ∧ pi σ ρ (Bp.P ρ) = Bp.P σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have h2σ : (2 : Ordinal.{0}) < σ :=
    (show (2 : Ordinal.{0}) < ω from natCast_lt_omega0 2).trans (omega0_lt_inE hB.1)
  obtain ⟨t1, t2⟩ := Bp.tP_pi σ ρ hB hγ
  have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 t1 (Bp.tP_T hB.2.1 hρ1 (hγ.trans hB.2.2.1)).2
  rw [pi_lt hB h2σ, t2] at h
  exact h

/-- **Lemma EXACT for `evZ(P(ρ))`** above the stage gate. -/
theorem evP_pi : evZ (Bp.P ρ) ∈ TB ρ σ ∧ pi σ ρ (evZ (Bp.P ρ)) = evZ (Bp.P σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hγρ : Bp.γP < ρ := hγ.trans hB.2.2.1
  have h2σ : (2 : Ordinal.{0}) < σ :=
    (show (2 : Ordinal.{0}) < ω from natCast_lt_omega0 2).trans (omega0_lt_inE hB.1)
  obtain ⟨t1, t2⟩ := Bp.tP_pi σ ρ hB hγ
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB t1 o1
  rw [t2, o2] at s2
  have h := glA_pi hB (mem_TB_of_lt hB h2σ) (gw_two_T hB.2.1 hρ1).2 s1
    (gm1_T hB.2.1 hρ1 (Bp.tP_lt ρ hB.2.1 hρ1 hγρ)).2
  rw [pi_lt hB h2σ, s2, ← Bp.evP hB.2.1 hρ1 hγρ, ← Bp.evP hB.1 hσ1 hγ] at h
  exact h

end Pi

end HaPB

/-! ## The stage at a `ζ`-index read by a system -/

section Of

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem ha_I0_add_lt {r : Ordinal.{0}} (hr : r < gzB3 x) : gzI0 x + r < gzB3 x :=
  (inE_indec (gzB3_E x)).add_lt ((gz_i0_lt hx hx1 (gzI0_spec x)).trans (gzZ1_lt_B3 x)) hr

theorem ha_veb_lt {r : Ordinal.{0}} (hr : r < gzB3 x) : veblen 2 (gzI0 x + r) < gzB3 x := by
  have h := (isNormal_veblen 2).strictMono (ha_I0_add_lt hx hx1 hr)
  rwa [gzB3_fix] at h

theorem ha_lt_q {r : Ordinal.{0}} (hr : r < gzB3 x) : lgG x + r < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (mg_lgG_lt_G1 hx hx1) (hr.trans (gzB3_lt1 hx hx1))

/-- **`ϑˣ(Ω₁·2 + Γ_{x+1} + r) = φ(2, i₀(x) + r)`** for every `r < B₃(x)`. -/
theorem ha_glA2 {r : Ordinal.{0}} (hr : r < gzB3 x) : glA 2 (lgG x + r) x = veblen 2 (gzI0 x + r) :=
  gz_glA2V hx hx1 (gzI0_spec x) r (ha_lt_q hx hx1 hr) fun ν' h' _ =>
    gz_nofix_B3 hx hx1 (gzI0_spec x) le_self_add
      (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt (ha_veb_lt hx hx1 hr))

theorem ha_R_B3 (E : GzVD) {l : Ordinal.{0}} (hlB : l < E.B) (hg : E.g l < x) : E.R l x < gzB3 x :=
  (E.R_lt_Z x hx hx1 l hlB hg).trans_le (E.Z_B3 x hx hx1)

end Of

theorem ha_G_lt_Q (l : Ordinal.{0}) : gcG 0 < veblen 2 (gcG 0 + 1 + l) := by
  have h := (isNormal_veblen 2).strictMono ((lt_add_one (gcG 0)).trans_le
    (le_self_add : gcG 0 + 1 ≤ gcG 0 + 1 + l))
  rwa [gn_veb_fix (gcG_SC 0) gw_two_lt_G] at h

theorem ha_Q_lt1 {l : Ordinal.{0}} (hl1 : l < gcG 1) : veblen 2 (gcG 0 + 1 + l + 1) < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC hG1
  refine hG1.2 2 (gw_two_lt_G.trans (gcG_lt zero_lt_one)) _ (hG1.add_one_lt ?_)
  exact (inE_indec hE).add_lt (hG1.add_one_lt (gcG_lt zero_lt_one)) hl1

/-- **THE STAGE AT THE `ζ`-INDEX `λ` READ BY `E`**: `Q = φ(2, G + 1 + λ)`, `t_P(x) = Γ_{x+1} + λ(x)`, gate `g_E(λ)`. -/
noncomputable def haPBof (E : GzVD) (l : Ordinal.{0}) (hlB : l < E.B)
    (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l)) : HaPB where
  jQ := gcG 0 + 1 + l
  tP := fun x => lgG x + E.R l x
  γP := E.g l
  γP_lt := E.g_lt l hlB
  jQ_mem := fun S a b ha hb => CSet.add_mem (CSet.succ_mem (gmS_G0_mem S ha)) (E.mem S a b ha l hlB hb).1
  jQ_cl := fun _ hZ hZ1 _ hy hQy hyZ => ha_cl_gate E hlB hZ hZ1 hj hy hQy hyZ
  jQ_lt := hj
  G_lt_Q := ha_G_lt_Q l
  Q_lt1 := ha_Q_lt1 (hlB.trans E.B_lt1)
  tP_lt := fun x hx hx1 hγ => (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt
    (ha_lt_q hx hx1 (ha_R_B3 hx hx1 E hlB hγ))
  tP_pi := fun σ ρ hB hγ => by
    obtain ⟨g1, g2⟩ : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := Go.goGl.ba_pi σ ρ hB
    obtain ⟨e1, e2⟩ := E.ex σ ρ hB l hlB hγ
    obtain ⟨s1, s2⟩ := pi_add hB g1 e1
    rw [g2, e2] at s2
    exact ⟨s1, s2⟩
  P_B3 := fun x hx hx1 hγ => by
    show glA 2 (lgG x + E.R l x) x < gzB3 x
    rw [ha_glA2 hx hx1 (ha_R_B3 hx hx1 E hlB hγ)]
    exact ha_veb_lt hx hx1 (ha_R_B3 hx hx1 E hlB hγ)

theorem haPBof_Q (E : GzVD) (l : Ordinal.{0}) (hlB : l < E.B) (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l)) :
    (haPBof E l hlB hj).Q = veblen 2 (gcG 0 + 1 + l) := rfl

theorem haPBof_γ (E : GzVD) (l : Ordinal.{0}) (hlB : l < E.B) (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l)) :
    (haPBof E l hlB hj).γP = E.g l := rfl

/-- **`P(x) = φ(2, i₀(x) + λ(x))`** above the gate of `λ`. -/
theorem haPBof_P (E : GzVD) (l : Ordinal.{0}) (hlB : l < E.B) (hj : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l))
    {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : E.g l < x) :
    (haPBof E l hlB hj).P x = veblen 2 (gzI0 x + E.R l x) :=
  ha_glA2 hx hx1 (ha_R_B3 hx hx1 E hlB hγ)

end Googology.Trans.PoR.InaccPsi.R2.Ha
