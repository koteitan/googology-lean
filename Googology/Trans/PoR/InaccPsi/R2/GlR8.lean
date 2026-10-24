import Googology.Trans.PoR.InaccPsi.R2.GlIm

/-!
# CODES BELOW `Γ_{Ω₁+1}` AS READING SYSTEMS: one reading, a bound `B`, layers, frontiers and the road

The reading `glR` is ONE function for every code below `Γ_{Ω₁+1}` (every level `1 ≤ α < Γ_{Ω₁+1}`).  A reading system
(`R2.GiRS`) needs a bound `B < Γ_{Ω₁+1}` (the hull atoms are `Γ_{Ω₁+1+c}`, `c < B`) with a cofinal sequence of
codes of gate `0` (`GlBd`); every such bound gives a reading system `glRS D` with the code system `glCS D`, the last
terms `gl_ld` with Lemma IMG for the logend (`glPkgG_of_ex`, below `Γ_{ρ+1}`).  The bounds `glBn n`: `glBn 0 =
φ(ω, Ω₁+1)`, `glBn (n+1) = φ(glBn n, 0)`, are cofinal in `Γ_{Ω₁+1}` (`glBn_cof`), so EVERY code below `Γ_{Ω₁+1}`
lies below the bound of some system.

* `glRr` (`glR` at the bases `x < Ω₁`, a strictly increasing stand-in above), `glRr_E`, `glRr_succ`, `glRr_mono`;
* `GlBd`, `glCS`, `gl_GiLD`, `glRr_GiLD`, `glRS`; `gl_omega_ge`, `glB_cof`, `glBn`, `glCfn`, `glBn_spec`, `glD`,
  `glBn_cof` (**`sup_n glBn n = Γ_{Ω₁+1}`**);
* `gl_spec` (**the gated layer of every code `c < Γ_{Ω₁+1}`**: top `Γ_{x+1+c(x)}`), `gl_loc` (**every code
  `c < Γ_{Ω₁+1}` with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`), `gl_zeta_eq`,
  `gl_zeta_loc` (**THE CODE `ζ_{Ω₁+1}` where round 82 stopped**), `gl_psi_loc` (every `φ(α, Ω₁+1)`, `α` of gate
  `0`), `gl_B0_loc` (the code `φ(ω, Ω₁+1)`, reading `VzB x`);
* `glW_sup` (**`sup = ι(Γ_{Ω₁+1+glBn n})`, `P(⋯) < L(0)`** for every `n`), `glFam_enum` (**ENUM-REACH**),
  `glFam_capV` (**CapV**), `glFam_blk` (**BLK^O and the exact reaches**), `glFam_road` (**THE ROAD**),
  `gl_fr_order`.

No new axiom.  New definitions: `glRr`, `GlBd`, `glCS`, `glRS`, `glBn`, `glCfn`, `glD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The reading used by the reading systems -/

/-- **The reading used by the reading systems**: `glR` at the bases `x < Ω₁`; at `x ≥ Ω₁` (where no layer is built)
a strictly increasing stand-in with the same value `ε_{x+1}` at `ε_{Ω₁+1}` and the same successor law. -/
noncomputable def glRr (c x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if x < Om1 then glR c x else if c < gfE then c else eN x + (c - gfE)

theorem glRr_eq {c x : Ordinal.{0}} (hx1 : x < Om1) : glRr c x = glR c x := by unfold glRr; rw [if_pos hx1]

theorem glRr_hi {c x : Ordinal.{0}} (hx1 : Om1 ≤ x) :
    glRr c x = if c < gfE then c else eN x + (c - gfE) := by unfold glRr; rw [if_neg (not_lt.2 hx1)]

theorem gl_sub_succ {c : Ordinal.{0}} (h : gfE ≤ c) : c + 1 - gfE = c - gfE + 1 := by
  have e1 : gfE + (c - gfE) = c := Ordinal.add_sub_cancel_of_le h
  have e2 : gfE + (c + 1 - gfE) = c + 1 := Ordinal.add_sub_cancel_of_le (h.trans (lt_add_one c).le)
  have : gfE + (c + 1 - gfE) = gfE + (c - gfE + 1) := by rw [e2, ← add_assoc, e1]
  exact (add_left_cancel_iff).1 this

theorem glRr_E (x : Ordinal.{0}) : glRr gfE x = eN x := by
  rcases lt_or_ge x Om1 with hx1 | hx1
  · rw [glRr_eq hx1, glR_E]
  · rw [glRr_hi hx1, if_neg (lt_irrefl _), Ordinal.sub_self, add_zero]

theorem glRr_succ (b x : Ordinal.{0}) : glRr (b + 1) x = glRr b x + 1 := by
  rcases lt_or_ge x Om1 with hx1 | hx1
  · rw [glRr_eq hx1, glRr_eq hx1, glR_succ_all]
  · rw [glRr_hi hx1, glRr_hi hx1]
    rcases lt_or_ge b gfE with hb | hb
    · rw [if_pos hb, if_pos ((ev_isSuccLimit_of_inE eW_E).add_one_lt hb)]
    · rw [if_neg (not_lt.2 hb), if_neg (not_lt.2 (hb.trans (lt_add_one b).le)), gl_sub_succ hb, add_assoc]

theorem glRr_mono {b c x : Ordinal.{0}} (hx : InE x) (hc : c < gcG 0) (hbc : b < c) (hgb : glG b < x)
    (hgc : glG c < x) : glRr b x < glRr c x := by
  rcases lt_or_ge x Om1 with hx1 | hx1
  · rw [glRr_eq hx1, glRr_eq hx1]; exact glR_mono hx hx1 hc hbc hgc hgb
  · rw [glRr_hi hx1, glRr_hi hx1]
    have hEx : gfE ≤ eN x := eN_le (hx1.trans_lt (lt_eN x)) (eN_E x)
    rcases lt_or_ge c gfE with hcE | hcE
    · rw [if_pos (hbc.trans hcE), if_pos hcE]; exact hbc
    rw [if_neg (not_lt.2 hcE)]
    rcases lt_or_ge b gfE with hbE | hbE
    · rw [if_pos hbE]; exact (hbE.trans_le hEx).trans_le le_self_add
    · rw [if_neg (not_lt.2 hbE)]
      refine (add_lt_add_iff_left _).2 ?_
      have e1 : gfE + (b - gfE) = b := Ordinal.add_sub_cancel_of_le hbE
      have e2 : gfE + (c - gfE) = c := Ordinal.add_sub_cancel_of_le hcE
      rw [← e1, ← e2] at hbc
      exact (add_lt_add_iff_left _).1 hbc

/-! ## Bounds and reading systems -/

/-- **A bound for a reading system**: `B < Γ_{Ω₁+1}`, a limit above `ε_{Ω₁+1}` in every hull, with a cofinal sequence
of codes of gate `0`. -/
structure GlBd where
  B : Ordinal.{0}
  B_lt : B < gcG 0
  E_lt : gfE < B
  B_lim : IsSuccLimit B
  B_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), B ∈ S.CSet a b
  cf : ℕ → Ordinal.{0}
  cf_ge : ∀ k, gfE ≤ cf k
  cf_lt : ∀ k, cf k < B
  cf_g : ∀ k, glG (cf k) = 0
  cf_mono : ∀ k, cf k < cf (k + 1)
  cf_cof : ∀ c, c < B → ∃ k, c < cf k

/-- **The code system below a bound.** -/
noncomputable def glCS (D : GlBd) : GiCS where
  B := D.B
  gt := glG
  B_lt := D.B_lt
  gt_zero := glG_zero
  gt_lt := fun c hc => glG_lt_Om1 c (hc.trans D.B_lt)
  gt_succ := fun b _ hZ hb hg => glG_succ hZ b (hb.trans D.B_lt) hg
  mem := fun _ _ _ c hc hg => (gl_mem c (hc.trans D.B_lt) hg).1
  B_mem := D.B_mem
  code_gate := fun _ _ hZ1 hZ0 hZa hZp hAt _ hc hcB =>
    gl_code_gate D.B_lt.le hZ1 hZ0 hZa hZp hAt D.E_lt.le hc hcB
  count := fun _ _ hc hy hy1 => gl_count (hc.trans D.B_lt.le) hy hy1

/-- **The field `ld`**: the last term of every limit code `c ∈ (ε_{Ω₁+1}, B)`, with Lemma IMG for its logend
(`glPkgG_of_ex`, from Lemma EXACT of the logend and the bound `Γ_{ρ+1}`). -/
theorem gl_GiLD (D : GlBd) : ∀ c, IsSuccLimit c → gfE < c → c < D.B → Nonempty (GiLD (glCS D) glR c) := by
  intro c hl hEc hcB
  have hc : c < gcG 0 := hcB.trans D.B_lt
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gl_ld c hl hc
  have hlg : ∀ x, InE x → x < Om1 → glG c < x → lg (glR c x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEc
  · show glG _ ≤ glG c
    split_ifs with h
    · exact hgcp
    · rw [glG_E]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      have hgcp' : gtc cp < x := by rw [← glG_low h]; exact hgcp.trans_lt hg
      rw [glR_E]
      exact e4.trans ((by rw [glR_low h]; exact rdc_lt_eN hx cp hgcp' : glR cp x < eN x)).le
  · intro ρ τ δ h hg
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < lgG ρ := by
      have h1 : T ρ ≤ glR c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (glR_lt_G hρE h.ρ1 hc hg)
    have hP := glPkgG_of_ex h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- The field `ld` for `glRr` (the data of `gl_GiLD`, read at the bases `x < Ω₁`). -/
theorem glRr_GiLD (D : GlBd) (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < D.B) :
    Nonempty (GiLD (glCS D) glRr c) := by
  obtain ⟨L⟩ := gl_GiLD D c hl hEc hc
  refine ⟨{
    cp := L.cp
    lp := L.lp
    cp_ge := L.cp_ge
    cp_lt := L.cp_lt
    cp_g := L.cp_g
    dec := fun x hx hx1 hg => by rw [glRr_eq hx1, glRr_eq hx1]; exact L.dec x hx hx1 hg
    pkg := fun ρ τ δ h hg => GhPkg.congr h (L.pkg ρ τ δ h hg)
      (fun y _ hy1 _ => by rw [glRr_eq hy1]) hg }⟩

/-- **THE READING SYSTEM below a bound `D`** (every `ε`-number code of every level below `D.B`). -/
noncomputable def glRS (D : GlBd) : GiRS where
  K := glCS D
  R := glRr
  E_lt := D.E_lt
  B_lim := D.B_lim
  gt_E := glG_E
  gt_lowE := fun _ hc => glG_low hc
  R_E := glRr_E
  lt0 := fun _ _ hx hx1 hc hg => by rw [glRr_eq hx1]; exact glR_lt0 hx hx1 (hc.trans D.B_lt) hg
  mono := fun _ _ _ hx hc hbc hgb hgc => glRr_mono hx (hc.trans D.B_lt) hbc hgb hgc
  succ := glRr_succ
  gt_le_succ := glG_le_succ_all
  cof := fun _ _ hx hx1 hc hEc hg _ hν => by
    rw [glRr_eq hx1] at hν
    obtain ⟨b, h1, h2, h3, h4⟩ := glR_cofE hx hx1 (hc.trans D.B_lt) hEc hg hν
    exact ⟨b, h1, h2, h3, by rw [glRr_eq hx1]; exact h4⟩
  ex := fun σ ρ c hB hc hg => by
    rw [glRr_eq hB.2.2.2, glRr_eq (hB.2.2.1.trans hB.2.2.2)]; exact gl_pi hB c (hc.trans D.B_lt) hg
  ld := glRr_GiLD D
  cf := D.cf
  cf_ge := D.cf_ge
  cf_lt := D.cf_lt
  cf_g := fun k => by rw [show (glCS D).gt = glG from rfl, D.cf_g k]; exact epsilon_pos 0
  cf_mono := D.cf_mono
  cf_cof := D.cf_cof

theorem glRS_V (D : GlBd) : (glRS D).K.V = gcG D.B := rfl

/-! ## The bounds `glBn n`, cofinal in `Γ_{Ω₁+1}` -/

/-- An ordinal `> Ω₁` in the range of `φ_o`, `o ≥ ω`, is at least `φ(ω, Ω₁+1)`. -/
theorem gl_omega_ge {o v : Ordinal.{0}} (ho : ω ≤ o) (hv : v ∈ Set.range (veblen o)) (hOv : Om1 < v) :
    glB ≤ v := by
  have hvω : v ∈ Set.range (veblen ω) := by
    rcases ho.lt_or_eq with h | h
    · obtain ⟨z, rfl⟩ := hv
      exact ⟨_, veblen_veblen_of_lt h z⟩
    · rw [h]; exact hv
  obtain ⟨z, rfl⟩ := hvω
  rcases le_or_gt z Om1 with hz | hz
  · have := (veblen_le_veblen_iff_right (o := ω)).2 hz
    rw [gl_veb_Om1 omega_lt_Om1] at this
    exact absurd hOv (not_lt.2 this)
  · exact (veblen_le_veblen_iff_right (o := ω)).2 (add_one_le_of_lt hz)

/-- `glPsi k 0 = φ(k, Ω₁+1)` for `1 ≤ k < Ω₁`. -/
theorem glPsi_zero {k : Ordinal.{0}} (hk : k < Om1) : glPsi k 0 = veblen k (Om1 + 1) := by
  unfold glPsi; rw [glLam_of_not (glFw_zero k), add_zero, glY0_lt hk]

/-- **`φ(ω, Ω₁+1) = sup_k φ(k, Ω₁+1)`**: every code below it is below some `φ(k, Ω₁+1)`. -/
theorem glB_cof {c : Ordinal.{0}} (hc : c < glB) : ∃ k : ℕ, c < veblen (k : Ordinal.{0}) (Om1 + 1) := by
  by_contra hcon
  push Not at hcon
  set g : ℕ → Ordinal.{0} := fun k => veblen (k : Ordinal.{0}) (Om1 + 1) with hgdef
  have hbdd : BddAbove (Set.range g) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hcon k⟩
  set S := ⨆ k, g k with hSdef
  have hSc : S ≤ c := Ordinal.iSup_le hcon
  have hfix : ∀ n : ℕ, veblen (n : Ordinal.{0}) S = S := by
    intro n
    refine le_antisymm ?_ (right_le_veblen _ _)
    rw [(isNormal_veblen _).map_iSup hbdd]
    refine Ordinal.iSup_le fun k => ?_
    have hm : (n : Ordinal.{0}) < ((max n k + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast (by omega : n < max n k + 1)
    have hk : (k : Ordinal.{0}) ≤ ((max n k + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast (by omega : k ≤ max n k + 1)
    calc veblen (n : Ordinal.{0}) (g k) ≤ veblen (n : Ordinal.{0}) (g (max n k + 1)) :=
          (veblen_le_veblen_iff_right).2 (veblen_left_monotone _ hk)
      _ = g (max n k + 1) := veblen_veblen_of_lt hm _
      _ ≤ S := Ordinal.le_iSup g _
  have hSω : S ∈ Set.range (veblen ω) :=
    (mem_range_veblen omega0_ne_zero).2 fun b hb => by obtain ⟨n, rfl⟩ := lt_omega0.1 hb; exact hfix n
  have hOS : Om1 < S := by
    have := Ordinal.le_iSup g 0
    simp only [hgdef, Nat.cast_zero, veblen_zero_apply] at this
    exact (lt_add_one Om1).trans_le ((right_le_opow _ one_lt_omega0).trans this)
  have h1 : glB ≤ S := gl_omega_ge le_rfl hSω hOS
  exact absurd (hc.trans_le (h1.trans hSc)) (lt_irrefl c)

/-- **The bounds**: `glBn 0 = φ(ω, Ω₁+1)`, `glBn (n+1) = φ(glBn n, 0)`. -/
noncomputable def glBn : ℕ → Ordinal.{0}
  | 0 => glB
  | n + 1 => veblen (glBn n) 0

/-- **The cofinal codes** of `glBn n`: `φ(k+1, Ω₁+1)` for `n = 0`, `φ(c, 0)` over the cofinal codes `c` of `n`. -/
noncomputable def glCfn : ℕ → ℕ → Ordinal.{0}
  | 0, k => glPsi ((k + 1 : ℕ) : Ordinal.{0}) 0
  | n + 1, k => veblen (glCfn n k) 0

theorem gl_veb0_psi {a : Ordinal.{0}} (hOa : Om1 < a) (haG : a < gcG 0) : veblen a 0 = glPsi a 0 := by
  unfold glPsi; rw [glLam_of_not (glFw_zero a), add_zero, glY0_gt hOa]

theorem gl_nat_cast_lt_G0 (k : ℕ) : ((k : ℕ) : Ordinal.{0}) < gcG 0 := (gl_nat_lt_Om1 k).trans gl_Om1_lt_G0

/-- **The facts on the bounds and their cofinal codes.** -/
theorem glBn_spec : ∀ n : ℕ, glBn n < gcG 0 ∧ gfE < glBn n ∧ InE (glBn n) ∧
    (∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), glBn n ∈ S.CSet a b) ∧
    (∀ k, gfE ≤ glCfn n k ∧ glCfn n k < glBn n ∧ glG (glCfn n k) = 0 ∧ glCfn n k < glCfn n (k + 1)) ∧
    (∀ c, c < glBn n → ∃ k, c < glCfn n k)
  | 0 => by
    have hEB : gfE < glB := by
      rw [eW_eq]
      calc veblen 1 (Om1 + 1) < veblen 1 glB := (veblen_lt_veblen_iff_right).2 (glB_lim.add_one_lt Om1_lt_glB)
        _ = glB := by unfold glB; exact veblen_veblen_of_lt one_lt_omega0 _
    refine ⟨glB_lt_G0, hEB, glB_E, fun _ _ _ => glB_mem, fun k => ?_, fun c hc => ?_⟩
    · have hk1 : (1 : Ordinal.{0}) ≤ ((k + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast Nat.succ_pos k
      have hkG := gl_nat_cast_lt_G0 (k + 1)
      have hkO := gl_nat_lt_Om1 (k + 1)
      refine ⟨gfE_le_glPsi hk1 hkG 0, ?_, ?_, ?_⟩
      · show glPsi _ 0 < glB
        rw [glPsi_zero hkO]
        calc veblen ((k + 1 : ℕ) : Ordinal.{0}) (Om1 + 1) < veblen ((k + 1 : ℕ) : Ordinal.{0}) glB :=
              (veblen_lt_veblen_iff_right).2 (glB_lim.add_one_lt Om1_lt_glB)
          _ = glB := by unfold glB; exact veblen_veblen_of_lt (natCast_lt_omega0 _) _
      · show glG (glPsi _ 0) = 0
        rw [glG_psi hk1 hkG gl_G0_E.pos, glQ_zero, glQ_nat, max_self]
      · show glPsi _ 0 < glPsi _ 0
        have hk2 : (1 : Ordinal.{0}) ≤ ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast Nat.succ_pos (k + 1)
        exact (glPsi_lt_lev (by exact_mod_cast Nat.lt_succ_self (k + 1)) hk2 (gl_nat_cast_lt_G0 _)).2
          (lt_of_le_of_lt zero_le (glPsi_gt hk2 (gl_nat_cast_lt_G0 _) 0).1)
    · obtain ⟨k, hk⟩ := glB_cof hc
      refine ⟨k, hk.trans_le ?_⟩
      show veblen _ _ ≤ glPsi _ 0
      rw [glPsi_zero (gl_nat_lt_Om1 (k + 1))]
      exact veblen_left_monotone _ (by exact_mod_cast Nat.le_succ k)
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := glBn_spec n
    have hBn1 : glBn (n + 1) = veblen (glBn n) 0 := rfl
    have hOn : Om1 < glBn n := Om1_lt_eW.trans h2
    refine ⟨?_, ?_, ?_, fun S a b => ?_, fun k => ?_, fun c hc => ?_⟩
    · rw [hBn1]; exact gl_veb_lt_G0 h1 gl_G0_E.pos
    · rw [hBn1]; exact h2.trans_le (by simpa using left_le_veblen (glBn n) 0)
    · rw [hBn1]
      have := veblen_veblen_of_lt (o₁ := 0) (o₂ := glBn n) (h3.pos) 0
      rw [veblen_zero_apply] at this; exact this
    · rw [hBn1]; exact CSet.phi_mem (h4 S a b) (CSet.zero_mem _ _)
    · obtain ⟨k1, k2, k3, k4⟩ := h5 k
      have hO : Om1 < glCfn n k := Om1_lt_eW.trans_le k1
      have hG : glCfn n k < gcG 0 := k2.trans h1
      have hc1 : glCfn (n + 1) k = veblen (glCfn n k) 0 := rfl
      have hc2 : glCfn (n + 1) (k + 1) = veblen (glCfn n (k + 1)) 0 := rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hc1]; exact k1.trans (by simpa using left_le_veblen (glCfn n k) 0)
      · rw [hc1, hBn1]; exact veblen_zero_lt_veblen_zero.2 k2
      · rw [hc1, gl_veb0_psi hO hG, glG_psi (one_le_iff_pos.2 (lt_of_le_of_lt zero_le hO)) hG gl_G0_E.pos,
          glQ_zero, max_eq_left zero_le]
        unfold glQ; split_ifs
        · rfl
        · exact k3
      · rw [hc1, hc2]; exact veblen_zero_lt_veblen_zero.2 k4
    · rw [hBn1] at hc
      have hlim : IsSuccLimit (glBn n) := ev_isSuccLimit_of_inE h3
      rw [(isNormal_veblen_zero).apply_of_isSuccLimit hlim] at hc
      obtain ⟨⟨a, ha⟩, hca⟩ := Ordinal.lt_iSup_iff.1 hc
      obtain ⟨k, hk⟩ := h6 a ha
      exact ⟨k, hca.trans (veblen_zero_lt_veblen_zero.2 hk)⟩

/-- **The bound `glBn n` with its cofinal codes.** -/
noncomputable def glD (n : ℕ) : GlBd where
  B := glBn n
  B_lt := (glBn_spec n).1
  E_lt := (glBn_spec n).2.1
  B_lim := ev_isSuccLimit_of_inE (glBn_spec n).2.2.1
  B_mem := (glBn_spec n).2.2.2.1
  cf := glCfn n
  cf_ge := fun k => ((glBn_spec n).2.2.2.2.1 k).1
  cf_lt := fun k => ((glBn_spec n).2.2.2.2.1 k).2.1
  cf_g := fun k => ((glBn_spec n).2.2.2.2.1 k).2.2.1
  cf_mono := fun k => ((glBn_spec n).2.2.2.2.1 k).2.2.2
  cf_cof := (glBn_spec n).2.2.2.2.2

/-- **`sup_n glBn n = Γ_{Ω₁+1}`**: every code below `Γ_{Ω₁+1}` lies below some bound `glBn n`. -/
theorem glBn_cof {c : Ordinal.{0}} (hc : c < gcG 0) : ∃ n, c < glBn n := by
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove (Set.range glBn) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hcon k⟩
  set S := ⨆ n, glBn n with hSdef
  have hSc : S ≤ c := Ordinal.iSup_le hcon
  have hfix : veblen S 0 = S := by
    refine le_antisymm ?_ (by simpa using left_le_veblen S 0)
    rw [(isNormal_veblen_zero).map_iSup hbdd]
    exact Ordinal.iSup_le fun n => Ordinal.le_iSup glBn (n + 1)
  have hOS : Om1 < S := Om1_lt_glB.trans_le (Ordinal.le_iSup glBn 0)
  have h1 := gl_G0_le (gl_SC_of_fix hfix (lt_of_le_of_lt zero_le hOS)) hOS
  exact absurd (hc.trans_le (h1.trans hSc)) (lt_irrefl c)

/-! ## The layers, the location, the frontiers and the road -/

/-- **THE GENERIC THEOREM for every code `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1})`**: a gated base package with gate `glG c` whose
top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at every `ε`-number base `x < Ω₁` above the gate. -/
theorem gl_spec : ∀ c, gfE ≤ c → c < gcG 0 → ∃ B : GdB, B.g = glG c ∧
    ∀ x, InE x → x < Om1 → glG c < x → B.K.E x = gq (glR c x) x ∧ B.K.sys.top x = gq (glR c x) x := by
  intro c h hc
  obtain ⟨n, hn⟩ := glBn_cof hc
  refine ⟨(glRS (glD n)).giL c h hn, (glRS (glD n)).giL_g h hn, fun x hx hx1 hg => ?_⟩
  have e1 := (glRS (glD n)).giL_E h hn hx hx1 hg
  have e2 := (glRS (glD n)).giL_top h hn hx hx1 hg
  rw [show (glRS (glD n)).R = glRr from rfl, glRr_eq hx1] at e1 e2
  exact ⟨e1, e2⟩

/-- **Every code `c ∈ [ε_{Ω₁+1}, B)` with gate below `ε₀` located** (any bound `D`): `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`,
`υ` of it `= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem gl_locD (D : GlBd) {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < D.B) (hg : glG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 ((glRS D).giX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 ((glRS D).giX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  (glRS D).giLoc c h hc hg S

/-- **EVERY CODE `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1})` WITH GATE BELOW `ε₀` LOCATED**: for the bound `glBn n` above it,
`Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem gl_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < gcG 0) (hg : glG c < ε₀) (S : InaccSeq.{0}) :
    ∃ n, ∃ hn : c < glBn n, xtB1 ((glRS (glD n)).giX c h hn hg) = iota S (gcG c * ω) ∧
      Pv S (gcG c * ω) < Nc.ncL S 0 := by
  obtain ⟨n, hn⟩ := glBn_cof hc
  obtain ⟨l1, -, l3⟩ := gl_locD (glD n) h hn hg S
  exact ⟨n, hn, l1, l3⟩

/-- **The code `φ(α, Ω₁+1)`** (`1 ≤ α < Ω₁` a constant level, e.g. `k < ω`): gate `glQ α`, reading `ϑˣ(Ω₁·α)`. -/
theorem gl_psi_read {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hαO : α < Om1) :
    gfE ≤ glPsi α 0 ∧ glPsi α 0 < gcG 0 ∧ glG (glPsi α 0) = glQ α ∧
      ∀ x, InE x → x < Om1 → glG α < x → glR (glPsi α 0) x = vt x (Om1 * glR α x + 0) := by
  have hαG : α < gcG 0 := hαO.trans gl_Om1_lt_G0
  refine ⟨gfE_le_glPsi hα1 hαG 0, glPsi_lt_G hαG gl_G0_E.pos, ?_, fun x hx hx1 hg => ?_⟩
  · rw [glG_psi hα1 hαG gl_G0_E.pos, glQ_zero, max_eq_left zero_le]
  · rw [glR_psi hα1 hαG gl_G0_E.pos, glR_zero, glBA_eq hx hx1]; rfl

/-- **THE CODE `ζ_{Ω₁+1} = φ(2, Ω₁+1)`** (round 82 stopped here) is `glPsi 2 0` and reads `ζ_{x+1} = ϑˣ(Ω₁·2)`. -/
theorem gl_zeta_eq : glPsi 2 0 = guB ∧ ∀ x, InE x → x < Om1 → glR guB x = evZ x := by
  have h2O : (2 : Ordinal.{0}) < Om1 := by exact_mod_cast gl_nat_lt_Om1 2
  have e : glPsi 2 0 = guB := by rw [glPsi_zero h2O, guB_eq]
  refine ⟨e, fun x hx hx1 => ?_⟩
  obtain ⟨-, -, -, hR⟩ := gl_psi_read (by norm_num) h2O
  have h2 : glR 2 x = 2 := by exact_mod_cast glR_nat 2 x
  have hg2 : glG 2 < x := by
    rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, glG_nat]
    exact (natCast_lt_omega0 2).trans (omega0_lt_inE hx)
  rw [← e, hR x hx hx1 hg2, h2]
  have := gl_vt_two hx hx1
  rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this

/-- **THE CODE `ζ_{Ω₁+1}` LOCATED** (where round 82 stopped): gate `0`, `Λ⁺ = ι(Γ_{Ω₁+1+ζ_{Ω₁+1}}·ω)`,
`P(⋯) < L(0)` (in the first reading system, bound `φ(ω, Ω₁+1)`). -/
theorem gl_zeta_loc (S : InaccSeq.{0}) :
    ∃ (h1 : gfE ≤ glPsi 2 0) (h2 : glPsi 2 0 < glBn 0) (h3 : glG (glPsi 2 0) < ε₀),
      xtB1 ((glRS (glD 0)).giX _ h1 h2 h3) = iota S (gcG guB * ω) ∧ Pv S (gcG guB * ω) < Nc.ncL S 0 := by
  have h2O : (2 : Ordinal.{0}) < Om1 := by exact_mod_cast gl_nat_lt_Om1 2
  obtain ⟨h1, -, hg, -⟩ := gl_psi_read (by norm_num) h2O
  have h2 : glPsi 2 0 < glBn 0 := by
    have := ((glBn_spec 0).2.2.2.2.1 1).2.1
    exact this
  have h3 : glG (glPsi 2 0) < ε₀ := by
    rw [hg]; unfold glQ; rw [if_pos (by exact_mod_cast natCast_lt_omega0 2)]; exact epsilon_pos 0
  obtain ⟨l1, -, l3⟩ := gl_locD (glD 0) h1 h2 h3 S
  exact ⟨h1, h2, h3, l1.trans (by rw [gl_zeta_eq.1]), by rw [← gl_zeta_eq.1]; exact l3⟩

/-- **`sup = ι(Γ_{Ω₁+1+glBn n})`, `υ` of it `= P(Γ_{Ω₁+1+glBn n}) < L(0)`** for every `n`. -/
theorem glW_sup (n : ℕ) (S : InaccSeq.{0}) : ((glRS (glD n)).giFam S).famSup = iota S (gcG (glBn n)) ∧
    upsilon ((glRS (glD n)).giFam S).famSup = Pv S (gcG (glBn n)) ∧ Pv S (gcG (glBn n)) < Nc.ncL S 0 :=
  (glRS (glD n)).giFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+glBn n})} = P(Γ_{Ω₁+1+glBn n})`**, with the exact reaches. -/
theorem glFam_blk (n : ℕ) (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon ((glRS (glD n)).giFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((glRS (glD n)).giFam S).famSup ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((glRS (glD n)).giFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((glRS (glD n)).giFam S).off k l)) ∧
    (∀ α < upsilon ((glRS (glD n)).giFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (glRS (glD n)).giFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+glBn n})`, fixed points included.** -/
theorem glFam_enum (n : ℕ) (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (glBn n))) : CdUpper S l ∧ CdLower S l := (glRS (glD n)).giFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+glBn n})`.** -/
theorem glFam_capV (n : ℕ) (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (glBn n))) : CdCapV S l := (glRS (glD n)).giFam_capV S hr hl

/-- **THE ROAD past every code below `glBn n`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+glBn n})`
(CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the
reaches. -/
theorem glFam_road (n : ℕ) (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (glBn n)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (glBn n)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (glBn n)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  (glRS (glD n)).giFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+glBn n}) < ι(Ω₂)` for every code `c < glBn n` with
gate below `ε₀`, and `P(Γ_{Ω₁+1+glBn n}) < P(Ω₂) < L(0)`. -/
theorem gl_fr_order (n : ℕ) {c : Ordinal.{0}} (hc : c < glBn n) (hg : glG c < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG c * ω) < iota S (gcG (glBn n)) ∧ iota S (gcG (glBn n)) < iota S (Om (1 + 1)) ∧
      Pv S (gcG (glBn n)) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  (glRS (glD n)).gi_fr_order hc hg S

end Googology.Trans.PoR.InaccPsi.R2.Gl
