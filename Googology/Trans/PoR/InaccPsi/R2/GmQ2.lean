import Googology.Trans.PoR.InaccPsi.R2.GmQ1

/-!
# THE CODES BELOW `Γ_{Ω₁+1}²` AS A READING SYSTEM: last terms, layers, frontiers and the road up to
`ι(Γ_{Γ_{Ω₁+1}²})`

* `gmPkg_add` (**Lemma IMG for a sum** `T₁ + T₂` from Lemma IMG for `T₁` and `T₂`, for the copies that keep the gate);
* `mqLD` (**the last term of every limit code in `(ε_{Ω₁+1}, Γ_{Ω₁+1}²)`**: below `Γ_{Ω₁+1}` from `Gl.gl_GiLD`; at
  `Γ_{Ω₁+1}·γ + c'` (`c'` a limit) the last term of `c'`; at `Γ_{Ω₁+1}·(γ''+1)` the logend `Γ_{x+1}`; at
  `Γ_{Ω₁+1}·γ` (`γ` a limit, `γ(x) = l' + ω^T`) the logend `Γ_{x+1} + T(x)`, Lemma IMG by `gmPkg_add`);
* `mqRS` (**THE READING SYSTEM** below `Γ_{Ω₁+1}²`, cofinal codes `Γ_{Ω₁+1}·c_k`, gate `0`);
* `mq_spec` (**the gated layer of every code `Γ_{Ω₁+1}·γ + c'`**: top `ϑˣ(Ω₁·Ω₁ + Γ_{x+1}·γ(x) + c'(x))`), `mq_loc`
  (**every such code with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`);
* `mqW_sup` (**`sup = ι(Γ_{Γ_{Ω₁+1}²})`, `P(Γ_{Γ_{Ω₁+1}²}) < L(0)`**), `mqFam_blk`, `mqFam_enum`, `mqFam_capV`,
  `mqFam_road`, `mq_fr_order` (**`ι(Γ_{Γ_{Ω₁+1}·ω}) < ι(Γ_{Γ_{Ω₁+1}²}) < ι(Ω₂)`**).

No new axiom.  New definition: `mqRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **Lemma IMG for a sum**, for the copies that keep the gate. -/
theorem gmPkg_add {g ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {T1 T2 : Ordinal.{0} → Ordinal.{0}} (h1 : GhPkg g ρ δ T1)
    (h2 : GhPkg g ρ δ T2) (hlt1 : T1 ρ < T1 ρ + T2 ρ) (hlt2 : T2 ρ < T1 ρ + T2 ρ) (hρ : ρ ≤ T1 ρ + T2 ρ) :
    GhPkg g ρ δ (fun x => T1 x + T2 x) := by
  classical
  obtain ⟨W1, Z1, w1, m1, i1⟩ := h1
  obtain ⟨W2, Z2, w2, m2, i2⟩ := h2
  have hρδ : ρ < δ := h.ρτ.trans h.τδ
  have hlt : ∀ {W Z : Finset Ordinal.{0}} {v : Ordinal.{0}}, WZ ρ δ W Z → v ∈ W ∪ Z → v < δ := by
    intro W Z v w hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact (w.1 v hv).2
    · exact (w.2.1 v hv).trans hρδ
  have hsδ : T1 ρ + T2 ρ < δ := (inE_indec h.δE).add_lt (hlt w1 m1) (hlt w2 m2)
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨insert (T1 ρ + T2 ρ) (W1 ∪ W2), Z1 ∪ Z2,
    (w1.union w2).insW hρ hsδ (Or.inr ⟨T1 ρ, hm _ (Or.inl m1), T2 ρ, hm _ (Or.inr m2), hlt1, hlt2, rfl⟩),
    by simp, ?_⟩
  intro A f hW hZ C
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hsA : T1 ρ + T2 ρ ∈ A := hW (by simp)
  have := C.add _ (mem_A m1 hW1 hZ1) _ (mem_A m2 hW2 hZ2) _ hsA rfl
  show T1 (f ρ) + T2 (f ρ) ≤ f (T1 ρ + T2 ρ)
  rw [← this]
  exact add_le_add (i1 A f hW1 hZ1 C) (i2 A f hW2 hZ2 C)

theorem mq_glQ_le_succ (a : Ordinal.{0}) : glQ a ≤ glQ (a + 1) := by
  unfold glQ
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact zero_le
  · exact absurd ((lt_add_one a).trans h2) h1
  · exact glG_le_succ_all a

theorem mq_glQ_inf {a : Ordinal.{0}} (h : ω ≤ a) : glQ a = glG a := by unfold glQ; rw [if_neg (not_lt.2 h)]

/-! ## The last terms -/

/-- **The last term of every limit code `c ∈ (ε_{Ω₁+1}, Γ_{Ω₁+1}²)`**, with Lemma IMG for its logend. -/
theorem mqLD (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < mqB) : Nonempty (GmLD mqCS mqR c) := by
  obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
  rcases eq_or_ne γ 0 with rfl | hγ0
  · -- below `Γ_{Ω₁+1}`
    have e0 : gcG 0 * 0 + c' = c' := by simp
    rw [e0] at hl hEc ⊢
    obtain ⟨n, hn⟩ := glBn_cof hc'
    obtain ⟨L⟩ := gl_GiLD (glD n) c' hl hEc hn
    have hcp : L.cp < gcG 0 := L.cp_lt.trans hc'
    refine ⟨{
      cp := L.cp
      lp := L.lp
      cp_ge := L.cp_ge
      cp_lt := L.cp_lt
      cp_g := by show mqG L.cp ≤ mqG c'; rw [mqG_low hcp, mqG_low hc']; exact L.cp_g
      dec := fun x hx hx1 hg => by
        show mqR c' x = _ ∧ _
        have hg' : glG c' < x := by rw [← mqG_low hc']; exact hg
        rw [mqR_low hc', mqR_low hcp]
        exact L.dec x hx hx1 hg'
      pkg := fun ρ τ δ h hg => by
        show GhPkg (mqG c') ρ δ (fun y => lg (mqR c' y))
        have hg' : glG c' < ρ := by rw [← mqG_low hc']; exact hg
        rw [mqG_low hc']
        exact GhPkg.congr h (L.pkg ρ τ δ h hg') (fun y _ _ _ => by rw [mqR_low hc']) hg' }⟩
  have hG0γ : gcG 0 ≤ gcG 0 * γ := le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 hγ0)
  have hEG : gfE ≤ gcG 0 * γ := gfE_lt_G0.le.trans hG0γ
  have hgates : ∀ {x : Ordinal.{0}}, InE x → x < Om1 → mqG (gcG 0 * γ + c') < x → glG γ < x ∧ glG c' < x :=
    fun hx hx1 hg => mq_gates hx hx1 (by rwa [mqG_split γ hc'] at hg)
  rcases Ordinal.zero_or_succ_or_isSuccLimit c' with h0 | ⟨d, hd⟩ | hlim
  · subst h0
    have hgc : mqG (gcG 0 * γ + 0) = glQ γ := by rw [mqG_split γ gl_G0_E.pos, glG_zero, max_eq_left zero_le]
    rcases Ordinal.zero_or_succ_or_isSuccLimit γ with hγ' | ⟨γ'', hγ''⟩ | hγl
    · exact absurd hγ' hγ0
    · -- `c = Γ_{Ω₁+1}·(γ''+1)`: logend `Γ_{x+1}`
      subst hγ''
      rw [Order.succ_eq_add_one] at *
      have hγ''G : γ'' < gcG 0 := (lt_add_one γ'').trans hγ
      have hR : ∀ x, mqR (gcG 0 * (γ'' + 1) + 0) x = lgG x * glR γ'' x + lgG x := fun x => by
        rw [mqR_split (γ'' + 1) gl_G0_E.pos x, glR_zero, add_zero, glR_succ_all, mul_add_one]
      have hlg : ∀ x, InE x → x < Om1 → lg (mqR (gcG 0 * (γ'' + 1) + 0) x) = lgG x := by
        intro x hx hx1
        have hE := (lgG_facts hx hx1).2.2.2.1
        have hd : lgG x * glR γ'' x + lgG x = lgG x * glR γ'' x + ω ^ lgG x := by rw [hE]
        rw [hR x, hd]
        exact Ge.lg_add_opow (by
          have := opow_dvd_opow ω (le_refl (lgG x)); rw [hE] at this ⊢; exact dvd_mul_of_dvd_left this _)
      have hpkg : ∀ ρ τ δ, RstK ρ τ δ → mqCS.gt (gcG 0 * (γ'' + 1) + 0) < ρ →
          GhPkg (mqCS.gt (gcG 0 * (γ'' + 1) + 0)) ρ δ (fun y => lg (mqR (gcG 0 * (γ'' + 1) + 0) y)) :=
        fun ρ τ δ h hg =>
          GhPkg.congr h (GhPkg.of_img (LgK.lgTopPkg h)) (fun y hyE hy1 _ => (hlg y hyE hy1).symm) hg
      have hdv : ∀ x, InE x → x < Om1 → ω ^ lgG x ∣ lgG x * glR γ'' x := fun x hx hx1 => by
        have hE := (lgG_facts hx hx1).2.2.2.1
        rw [hE]; exact dvd_mul_right _ _
      rcases eq_or_ne γ'' 0 with rfl | hγ''0
      · refine ⟨{
          cp := gfE
          lp := fun _ => 0
          cp_ge := le_rfl
          cp_lt := by rw [zero_add, mul_one, add_zero]; exact gfE_lt_G0
          cp_g := by show mqG gfE ≤ _; rw [mqG_E]; exact zero_le
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        refine ⟨?_, dvd_zero _, ?_, zero_le⟩
        · rw [hlg x hx hx1, hR x, glR_zero, mul_zero, zero_add, (lgG_facts hx hx1).2.2.2.1, zero_add]
        · rw [hlg x hx hx1]; exact (lgG_pos hx hx1).ne'
      · refine ⟨{
          cp := gcG 0 * γ'' + 0
          lp := fun x => lgG x * glR γ'' x
          cp_ge := by rw [add_zero]; exact gfE_lt_G0.le.trans (le_mul_of_one_le_right'
            (Order.one_le_iff_ne_zero.2 hγ''0))
          cp_lt := by
            rw [add_zero, add_zero]
            exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (lt_add_one γ'')
          cp_g := by
            show mqG _ ≤ mqG _
            rw [mqG_split γ'' gl_G0_E.pos, mqG_split (γ'' + 1) gl_G0_E.pos]
            exact max_le_max (mq_glQ_le_succ γ'') le_rfl
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlg x hx hx1, hR x, (lgG_facts hx hx1).2.2.2.1]
        · rw [hlg x hx hx1]; exact hdv x hx hx1
        · rw [hlg x hx hx1]; exact (lgG_pos hx hx1).ne'
        · rw [mqR_split γ'' gl_G0_E.pos x, glR_zero, add_zero]
    · -- `c = Γ_{Ω₁+1}·γ`, `γ` a limit: logend `Γ_{x+1} + T(x)`
      obtain ⟨cpγ, lpγ, T, hcp, hgcp, hdec, hex⟩ := gl_ld γ hγl hγ
      have hωγ : ω ≤ γ := omega0_le_of_isSuccLimit hγl
      have hgc' : mqG (gcG 0 * γ + 0) = glG γ := by rw [hgc, mq_glQ_inf hωγ]
      have hcpG : cpγ < gcG 0 := hcp.trans hγ
      have hR : ∀ x, InE x → x < Om1 → glG γ < x →
          mqR (gcG 0 * γ + 0) x = lgG x * lpγ x + ω ^ (lgG x + T x) := fun x hx hx1 hg => by
        obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
        rw [mqR_split γ gl_G0_E.pos x, glR_zero, add_zero, e1, mul_add, opow_add,
          (lgG_facts hx hx1).2.2.2.1]
      have hdv : ∀ x, InE x → x < Om1 → glG γ < x → ω ^ (lgG x + T x) ∣ lgG x * lpγ x := fun x hx hx1 hg => by
        obtain ⟨-, e2, -, -⟩ := hdec x hx hx1 hg
        obtain ⟨m, hm⟩ := e2
        refine ⟨m, ?_⟩
        rw [hm, ← mul_assoc, opow_add, (lgG_facts hx hx1).2.2.2.1]
      have hlg : ∀ x, InE x → x < Om1 → glG γ < x → lg (mqR (gcG 0 * γ + 0) x) = lgG x + T x :=
        fun x hx hx1 hg => by rw [hR x hx hx1 hg]; exact Ge.lg_add_opow (hdv x hx hx1 hg)
      have hTl : ∀ x, InE x → x < Om1 → glG γ < x → T x < lgG x := fun x hx hx1 hg => by
        obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
        have h1 : T x ≤ glR γ x := by rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
        exact h1.trans_lt (glR_lt_G hx hx1 hγ hg)
      have hpkg : ∀ ρ τ δ, RstK ρ τ δ → mqCS.gt (gcG 0 * γ + 0) < ρ →
          GhPkg (mqCS.gt (gcG 0 * γ + 0)) ρ δ (fun y => lg (mqR (gcG 0 * γ + 0) y)) := by
        intro ρ τ δ h hg
        have hg' : glG γ < ρ := by rw [← hgc']; exact hg
        have hρE := upsPt_inE h.ρU
        obtain ⟨-, e2', e3', -⟩ := hdec ρ hρE h.ρ1 hg'
        have hP2 : GhPkg (mqCS.gt (gcG 0 * γ + 0)) ρ δ T :=
          glPkgG_of_ex h (C := ∅) hg (by simp) (hTl ρ hρE h.ρ1 hg')
            (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB (by
              have : glG γ = mqCS.gt (gcG 0 * γ + 0) := hgc'.symm
              rw [this]; exact hgσ))
        have hP1 : GhPkg (mqCS.gt (gcG 0 * γ + 0)) ρ δ lgG := GhPkg.of_img (LgK.lgTopPkg h)
        have hT0 : 0 < T ρ := pos_iff_ne_zero.2 e3'
        have hP := gmPkg_add h hP1 hP2 (lt_add_of_pos_right _ hT0)
          ((hTl ρ hρE h.ρ1 hg').trans_le le_self_add) ((lgG_facts hρE h.ρ1).2.1.le.trans le_self_add)
        exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 (by rw [← hgc']; exact hgy)).symm) hg
      rcases eq_or_ne cpγ 0 with hcp0 | hcp0
      · refine ⟨{
          cp := gfE
          lp := fun x => lgG x * lpγ x
          cp_ge := le_rfl
          cp_lt := lt_of_lt_of_le gfE_lt_G0 (hG0γ.trans le_self_add)
          cp_g := by show mqG gfE ≤ _; rw [mqG_E]; exact zero_le
          dec := fun x hx hx1 hg => ?_
          pkg := hpkg }⟩
        have hg' : glG γ < x := by rw [← hgc']; exact hg
        obtain ⟨-, -, e3, e4⟩ := hdec x hx hx1 hg'
        rw [hcp0, glR_zero] at e4
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
        · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
        · rw [hlg x hx hx1 hg']
          exact (lt_of_lt_of_le (lgG_pos hx hx1) le_self_add).ne'
        · rw [le_zero_iff.1 e4, mul_zero]; exact zero_le
      · refine ⟨{
          cp := gcG 0 * cpγ + 0
          lp := fun x => lgG x * lpγ x
          cp_ge := by rw [add_zero]; exact gfE_lt_G0.le.trans (le_mul_of_one_le_right'
            (Order.one_le_iff_ne_zero.2 hcp0))
          cp_lt := by
            rw [add_zero, add_zero]; exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 hcp
          cp_g := by
            show mqG _ ≤ mqG _
            rw [mqG_split cpγ gl_G0_E.pos, hgc', glG_zero, max_eq_left zero_le]
            exact (glQ_le _).trans hgcp
          dec := fun x hx hx1 hg => ?_
          pkg := hpkg }⟩
        have hg' : glG γ < x := by rw [← hgc']; exact hg
        obtain ⟨-, -, e3, e4⟩ := hdec x hx hx1 hg'
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
        · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
        · rw [hlg x hx hx1 hg']
          exact (lt_of_lt_of_le (lgG_pos hx hx1) le_self_add).ne'
        · rw [mqR_split cpγ gl_G0_E.pos x, glR_zero, add_zero]; exact mul_le_mul_left' e4 _
  · exfalso
    subst hd
    have hlt : gcG 0 * γ + d < gcG 0 * γ + Order.succ d := (add_lt_add_iff_left _).2 (Order.lt_succ d)
    have := hl.add_one_lt hlt
    rw [Order.succ_eq_add_one, ← add_assoc] at this
    exact lt_irrefl _ this
  · -- `c' > 0` a limit: the last term of `c'`
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gl_ld c' hlim hc'
    have hcpG : cp < gcG 0 := hcp.trans hc'
    have hTl : ∀ x, InE x → x < Om1 → glG c' < x → T x < lgG x := fun x hx hx1 hg => by
      obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
      have h1 : T x ≤ glR c' x := by rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (glR_lt_G hx hx1 hc' hg)
    have hdv : ∀ x, InE x → x < Om1 → glG c' < x → ω ^ T x ∣ lgG x * glR γ x + lp x := fun x hx hx1 hg => by
      obtain ⟨-, e2, -, -⟩ := hdec x hx hx1 hg
      have hE := (lgG_facts hx hx1).2.2.2.1
      have h1 : ω ^ T x ∣ lgG x := by
        have := opow_dvd_opow ω (hTl x hx hx1 hg).le; rwa [hE] at this
      exact dvd_add (dvd_mul_of_dvd_left h1 _) e2
    have hR : ∀ x, InE x → x < Om1 → glG c' < x →
        mqR (gcG 0 * γ + c') x = (lgG x * glR γ x + lp x) + ω ^ T x := fun x hx hx1 hg => by
      obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
      rw [mqR_split γ hc' x, e1, add_assoc]
    have hlg : ∀ x, InE x → x < Om1 → glG c' < x → lg (mqR (gcG 0 * γ + c') x) = T x :=
      fun x hx hx1 hg => by rw [hR x hx hx1 hg]; exact Ge.lg_add_opow (hdv x hx hx1 hg)
    refine ⟨{
      cp := gcG 0 * γ + cp
      lp := fun x => lgG x * glR γ x + lp x
      cp_ge := hEG.trans le_self_add
      cp_lt := (add_lt_add_iff_left _).2 hcp
      cp_g := by
        show mqG _ ≤ mqG _
        rw [mqG_split γ hcpG, mqG_split γ hc']; exact max_le_max le_rfl hgcp
      dec := fun x hx hx1 hg => ?_
      pkg := fun ρ τ δ h hg => ?_ }⟩
    · have hg' : glG c' < x := (hgates hx hx1 hg).2
      obtain ⟨-, -, e3, e4⟩ := hdec x hx hx1 hg'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
      · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
      · rw [hlg x hx hx1 hg']; exact e3
      · rw [mqR_split γ hcpG x]; exact add_le_add_right e4 _
    · have hρE := upsPt_inE h.ρU
      have hg' : glG c' < ρ := (hgates hρE h.ρ1 hg).2
      have hP := glPkgG_of_ex h (C := ∅) hg (by simp) (hTl ρ hρE h.ρ1 hg')
        (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB (lt_of_le_of_lt (by
          show glG c' ≤ mqG (gcG 0 * γ + c'); rw [mqG_split γ hc']; exact le_max_right _ _) hgσ))
      exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 (hgates hyE hy1 hgy).2).symm) hg

end Googology.Trans.PoR.InaccPsi.R2.Gm
