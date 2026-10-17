import Googology.Trans.PoR.InaccPsi.R2.XtVz
import Googology.Trans.PoR.InaccPsi.R2.XtB
import Googology.Trans.PoR.InaccPsi.R2.XtPow

/-!
# One more term layer, generically: from a term system with top `T(x) = ω^{E(x)}` to the terms `T(x)·γ + s(x)`

A **layer** (`XtLay`) is a term system (`R2.XtGen`) whose top is a power `T(x) = ω^{E(x)}` with `ω^x ∣ E(x)`, with
Lemma EXACT for its terms and for `E`, and a witness pair for `T(ρ)` that makes every covering copy `f(T(ρ))` a power
`ω^{e'}` with `ω^{f(ρ)} ∣ e'` and `T(f(ρ)) ≤ f(T(ρ))`.  Then (`XtLay.xtNext`) the terms `T(x)·γ + s(x)` (`γ` a constant,
`s` a term of the layer) form a layer with top `T(x)·x = ω^{E(x)+x}`:

* the order is lexicographic (`xt1_lex_le`), every ordinal below `T(ρ)·ρ` is a value (division by `T(ρ)`);
* **EXACT**: `π_{σ,ρ}(T(ρ)·γ + s(ρ)) = T(σ)·γ + s(σ)` (`xtPiOpowMul`, `pi_add`);
* **IMG**: `f(T(ρ)·γ + s(ρ)) ≥ T(f(ρ))·γ + s(f(ρ))` (`xtLMul` with the witness pair of `T(ρ)`, the package of `s`);
* **RS**: Lemma RS for every new term (`rs_rstF` with EXACT);
* the witness pair of the new top: the atom `T(ρ)·ρ ≤₁ T(ρ)·ρ + ρ` of `R₁⁺` ([W07b] Theorem 2.2) is kept by the copy,
  so `f(T(ρ)·ρ) = ω^a` with `ω^{f(ρ)} ∣ a`, `a ≥ e' + f(ρ)`, `f(T(ρ)·ρ) ≥ f(T(ρ))·f(ρ)`.

The base layer is `vzLay` (the terms `φ(n, ·)`, `n < ω`, top `B(x) = ω^{B(x)}`); `xtLayN n` is the `n`-th layer, with
top `B(x)·x^n` (`xtLayN_top`).

The only new axiom used is `xtOm1w_TB` (`R2.CitedXt`, through `xtPiB`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **A term layer**: a term system with top `ω^{E(x)}`, EXACT, and a witness pair for the top. -/
structure XtLay where
  sys : XtSys
  E : Ordinal.{0} → Ordinal.{0}
  top_eq : ∀ x, InE x → x < Om1 → sys.top x = ω ^ E x
  exp_dvd : ∀ x, InE x → x < Om1 → ω ^ x ∣ E x
  exp_lt : ∀ x, InE x → x < Om1 → E x < Om1
  top_gt : ∀ x, InE x → x < Om1 → x < sys.top x
  top_lt_ups : ∀ x u, InE x → x < Om1 → x < u → UpsPt u → sys.top x < u
  lt_top_E : ∀ x, InE x → x < Om1 → ∀ t, sys.CB t x → sys.val t x < sys.top x
  exact : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → ∀ t, sys.CB t σ →
    sys.val t ρ ∈ TB ρ σ ∧ pi σ ρ (sys.val t ρ) = sys.val t σ
  exp_pi : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → E ρ ∈ TB ρ σ ∧ pi σ ρ (E ρ) = E σ
  top_wit : ∀ ρ τ δ, RstK ρ τ δ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ sys.top ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (sys.top ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ sys.top (f ρ) ≤ f (sys.top ρ)

/-- **The base layer**: the terms `φ(n, ·)`, `n < ω`, top `B(x) = ω^{B(x)}`. -/
noncomputable def vzLay : XtLay where
  sys := vzSys
  E := VzB
  top_eq := fun x hx hx1 => (xt_B_E hx hx1).symm
  exp_dvd := fun x hx hx1 => opow_dvd_of_inE (xt_B_E hx hx1) (vzB_omega hx hx1).2.1.le
  exp_lt := fun x hx hx1 => xt_B_lt_Om1 hx hx1
  top_gt := fun x hx hx1 => (vzB_omega hx hx1).2.1
  top_lt_ups := fun _ _ hx hx1 hxu hu => xt_B_lt_ups hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 _ ht => vzv_lt_B hx hx1 ht
  exact := fun _ _ hσ hρ hB t ht => vzv_pi hσ hρ hB t ht
  exp_pi := fun _ _ _ _ hB => xtPiB hB
  top_wit := fun ρ τ δ h => by
    obtain ⟨hw, hm, hI⟩ := xtWitB h
    refine ⟨_, ∅, hw, hm, fun A f hW hZ C => ?_⟩
    obtain ⟨hE, hle⟩ := hI A f hW hZ C
    have hρB : f ρ ≤ f (VzB ρ) := (C.mono C.rho (hW (by simp)) (vzB_omega h.ρE h.ρ1).2.1).le
    exact ⟨⟨f (VzB ρ), hE.symm, opow_dvd_of_inE hE hρB⟩, hle⟩

namespace XtLay

variable (L : XtLay)

/-- The value `T(x)·γ + s(x)` of the next layer. -/
noncomputable def nval (p : Ordinal.{0} × L.sys.Tm) (x : Ordinal.{0}) : Ordinal.{0} :=
  L.sys.top x * p.1 + L.sys.val p.2 x

/-- The constants below `x`. -/
def nCB (p : Ordinal.{0} × L.sys.Tm) (x : Ordinal.{0}) : Prop := p.1 < x ∧ L.sys.CB p.2 x

/-- The constants. -/
def ncs (p : Ordinal.{0} × L.sys.Tm) : List Ordinal.{0} := p.1 :: L.sys.cs p.2

variable {L}

theorem nval_zero (s : L.sys.Tm) : L.nval (0, s) = L.sys.val s := by
  funext x; simp [nval]

theorem ncb_cst (p : Ordinal.{0} × L.sys.Tm) (x : Ordinal.{0}) (h : L.nCB p x) :
    ∀ c ∈ L.ncs p, c < x := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact h.1
  · exact L.sys.cb_cst p.2 x h.2 c hc

theorem ncb_iff (p : Ordinal.{0} × L.sys.Tm) (x x' : Ordinal.{0}) (h : L.nCB p x)
    (h' : ∀ c ∈ L.ncs p, c < x') : L.nCB p x' :=
  ⟨h' p.1 List.mem_cons_self, L.sys.cb_iff p.2 x x' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩

theorem T_pos {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : 0 < L.sys.top x :=
  hx.pos.trans (L.top_gt x hx hx1)

theorem nsmall (p : Ordinal.{0} × L.sys.Tm) :
    (∀ x y, L.nval p x = L.nval p y) ∨ (∀ x, InE x → x < Om1 → L.nCB p x → x ≤ L.nval p x) := by
  obtain ⟨γ, s⟩ := p
  rcases eq_or_ne γ 0 with rfl | hγ
  · rw [nval_zero]
    rcases L.sys.small s with h | h
    · exact Or.inl h
    · exact Or.inr (fun x hx hx1 hc => h x hx hx1 hc.2)
  · refine Or.inr (fun x hx hx1 _ => ?_)
    exact ((L.top_gt x hx hx1).le.trans (le_mul_left _ (pos_iff_ne_zero.2 hγ))).trans le_self_add

theorem nlt_top_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (p : Ordinal.{0} × L.sys.Tm)
    (h : L.nCB p x) : L.nval p x < L.sys.top x * x := by
  have := (xt1_lex_lt (b := L.sys.top x) (γ := p.1) (γ' := x) (a' := 0)
    (L.lt_top_E x hx hx1 p.2 h.2) (T_pos hx hx1)).2 (Or.inl h.1)
  simpa [nval] using this

theorem ntop_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    L.sys.top x * x < u :=
  (upsPt_inE hu).mul_lt (L.top_lt_ups x u hx hx1 hxu hu) hxu

/-- **Lemma EXACT for `T(x)·γ`** (`γ < σ`). -/
theorem npiT {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {γ : Ordinal.{0}}
    (hγ : γ < σ) : L.sys.top ρ * γ ∈ TB ρ σ ∧ pi σ ρ (L.sys.top ρ * γ) = L.sys.top σ * γ := by
  have hσ1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
  rw [L.top_eq ρ hB.2.1 hB.2.2.2, L.top_eq σ hB.1 hσ1]
  exact xtPiOpowMul hσ hρ hB h1 h2 (L.exp_lt ρ hB.2.1 hB.2.2.2) γ hγ

/-- **Lemma EXACT for the terms of the next layer.** -/
theorem nexact {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (p : Ordinal.{0} × L.sys.Tm) (h : L.nCB p σ) :
    L.nval p ρ ∈ TB ρ σ ∧ pi σ ρ (L.nval p ρ) = L.nval p σ := by
  obtain ⟨h1, h2⟩ := npiT (L := L) hσ hρ hB h.1
  obtain ⟨h3, h4⟩ := L.exact σ ρ hσ hρ hB p.2 h.2
  obtain ⟨h5, h6⟩ := pi_add hB h1 h3
  exact ⟨h5, by rw [nval, h6, h2, h4]; rfl⟩

/-- **The witness pair of `T(ρ)·γ`**: `f(T(ρ)·γ) ≥ T(f(ρ))·γ` for `γ < ρ`. -/
theorem nwitT {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {γ : Ordinal.{0}} (hγ : γ < ρ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (γ ≠ 0 → L.sys.top ρ * γ ∈ W) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → L.sys.top (f ρ) * γ ≤ f (L.sys.top ρ * γ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨Wt, Zt, hwt, htW, hIt⟩ := L.top_wit ρ τ δ h
  have hTe := L.top_eq ρ hρE hρ1
  have hρT : ρ < L.sys.top ρ := L.top_gt ρ hρE hρ1
  have hTδ : L.sys.top ρ < δ := L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1
  have he0 : L.E ρ ≠ 0 := by
    intro h0
    rw [hTe, h0, opow_zero] at hρT
    exact absurd hρT (not_lt.2 (one_lt_of_upsPt h.ρU).le)
  rw [hTe] at htW hρT hTδ
  obtain ⟨W, Z, hw, hγW, hbW, hbZ, hI⟩ := xtLMul h he0 hρT.le hTδ (L.exp_dvd ρ hρE hρ1) hwt htW
    (fun A f hW hZ C => by have := (hIt A f hW hZ C).1; rwa [hTe] at this) γ hγ
  refine ⟨W, insert γ Z, hw.insZ hγ, fun h0 => by rw [hTe]; exact hγW h0, fun A f hW hZ C => ?_⟩
  have hZA : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hγA : γ ∈ A := hZ (by simp)
  have hγf : γ < f ρ := C.above γ hγA hγ
  have h1 := hI A f hW hZA C hγf
  have h2 := (hIt A f (fun x hx => hW (hbW hx)) (fun x hx => hZA (hbZ hx)) C).2
  rw [hTe] at h2 ⊢
  exact (mul_le_mul_left h2 γ).trans h1

/-- **Lemma IMG for the terms of the next layer.** -/
theorem npkg {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (p : Ordinal.{0} × L.sys.Tm)
    (hCB : L.nCB p (upsilon l)) (h1 : 1 ≤ L.nval p (upsilon l))
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (L.nval p) := by
  classical
  obtain ⟨γ, s⟩ := p
  set ρ := upsilon l with hρ
  set δ := upsilon (l + ω + 1) with hδ
  have hρE := R.ρE
  have hρ1 := R.ρ1
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [nval_zero] at h1 ⊢
    exact L.sys.pkg l hl hl1 s hCB.2 h1 R
  have hγρ : γ < ρ := hCB.1
  have hsT : L.sys.val s ρ < L.sys.top ρ := L.lt_top_E ρ hρE hρ1 s hCB.2
  have hρT : ρ < L.sys.top ρ := L.top_gt ρ hρE hρ1
  have hTγ : L.sys.top ρ ≤ L.sys.top ρ * γ := le_mul_left _ (pos_iff_ne_zero.2 hγ0)
  have hvδ : L.nval (γ, s) ρ < δ :=
    (nlt_top_E hρE hρ1 (γ, s) hCB).trans
      ((ntop_lt_ups hρE hρ1 R.ρτ R.τU).trans R.τδ)
  obtain ⟨W1, Z1, hw1, hγW, hI1⟩ := nwitT (L := L) R hγρ
  have hTγW : L.sys.top ρ * γ ∈ W1 := hγW hγ0
  rcases eq_or_ne (L.sys.val s ρ) 0 with hs0 | hs0
  · have hconst : ∀ y, L.sys.val s y = 0 := by
      rcases L.sys.small s with hc | hc
      · intro y; rw [hc y ρ, hs0]
      · have := hc ρ hρE hρ1 hCB.2
        rw [hs0] at this
        exact absurd this (not_le.2 hρE.pos)
    refine ⟨h1, hvδ, W1, Z1, hw1, ?_, fun A f hW hZ C => ?_⟩
    · simp only [nval, hs0, add_zero]; exact Finset.mem_union_left _ hTγW
    · simp only [nval, hconst, add_zero]
      exact hI1 A f hW hZ C
  · have hs1 : 1 ≤ L.sys.val s ρ := one_le_iff_ne_zero.2 hs0
    obtain ⟨-, -, W2, Z2, hw2, hsm0, hI2⟩ := L.sys.pkg l hl hl1 s hCB.2 hs1 R
    have hsm : L.sys.val s ρ ∈ W2 ∪ Z2 := hsm0
    have hpos : 0 < L.sys.val s ρ := pos_iff_ne_zero.2 hs0
    have hsγ : L.sys.val s ρ < L.sys.top ρ * γ := hsT.trans_le hTγ
    have hsum : L.nval (γ, s) ρ = L.sys.top ρ * γ + L.sys.val s ρ := rfl
    have hw : WZ ρ δ (insert (L.sys.top ρ * γ + L.sys.val s ρ) (W1 ∪ W2)) (Z1 ∪ Z2) := by
      refine (hw1.union hw2).insW ((hρT.le.trans hTγ).trans le_self_add) (hsum ▸ hvδ) (Or.inr ?_)
      refine ⟨L.sys.top ρ * γ, by simp [hTγW], L.sys.val s ρ, ?_, lt_add_of_pos_right _ hpos,
        hsγ.trans_le le_self_add, rfl⟩
      rcases Finset.mem_union.1 hsm with h | h <;> simp [h]
    refine ⟨h1, hvδ, _, _, hw, by simp [hsum], fun A f hW hZ C => ?_⟩
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hTA : L.sys.top ρ * γ ∈ A := hW1 hTγW
    have hsA : L.sys.val s ρ ∈ A := mem_A hsm hW2 hZ2
    have hpA : L.sys.top ρ * γ + L.sys.val s ρ ∈ A := hW (by simp)
    have hadd := C.add _ hTA _ hsA _ hpA rfl
    show L.sys.top (f ρ) * γ + L.sys.val s (f ρ) ≤ f (L.sys.top ρ * γ + L.sys.val s ρ)
    rw [← hadd]
    exact add_le_add (hI1 A f hW1 hZ1 C) (hI2 A f hW2 hZ2 C)

/-- **Lemma RS for the terms of the next layer.** -/
theorem nrs {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (p : Ordinal.{0} × L.sys.Tm)
    (hCB : L.nCB p (upsilon l)) : RsStep l (L.nval p) := by
  classical
  obtain ⟨γ, s⟩ := p
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [nval_zero]; exact L.sys.rs l hl hl1 s hCB.2
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have hnx := upsilon_isNext l
  have hCs : ∀ σ, (∀ c ∈ (L.ncs (γ, s)).toFinset, c < σ) → L.nCB (γ, s) σ := fun σ hσ =>
    ncb_iff _ _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
  refine rs_rstF (T := L.nval (γ, s)) (C := (L.ncs (γ, s)).toFinset) R
    (fun c hc => ncb_cst _ _ hCB c (List.mem_toFinset.1 hc)) ?_ ?_ ?_ ?_ htg
  · exact ((L.top_gt _ hρE hρ1).le.trans (le_mul_left _ (pos_iff_ne_zero.2 hγ0))).trans le_self_add
  · have hU := hnx.2.1
    have hE := upsPt_inE hU
    have hTu := L.top_lt_ups _ _ hρE hρ1 hnx.1 hU
    have hγu : γ < upsilon (succ l) := hCB.1.trans hnx.1
    have hsu : L.sys.val s (upsilon l) < upsilon (succ l) := (L.lt_top_E _ hρE hρ1 s hCB.2).trans hTu
    exact (inE_indec hE).add_lt (hE.mul_lt hTu hγu) hsu
  · intro σ hσ hB hCσ _
    exact (nexact hσ R.ρU hB (γ, s) (hCs σ hCσ)).2
  · intro σ hσE hσρ _ hCσ
    obtain ⟨hcγ, hcs⟩ := hCs σ hCσ
    have hσ1 := hσρ.trans hρ1
    have hTρ := L.top_lt_ups σ _ hσE hσ1 hσρ R.ρU
    show L.sys.top σ * γ + L.sys.val s σ < upsilon l
    exact (inE_indec hρE).add_lt (hρE.mul_lt hTρ (hcγ.trans hσρ))
      ((L.lt_top_E σ hσE hσ1 s hcs).trans hTρ)

/-- **The term system of the next layer**: `T(x)·γ + s(x)`, top `T(x)·x`. -/
noncomputable def nsys (L : XtLay) : XtSys where
  Tm := Ordinal.{0} × L.sys.Tm
  val := L.nval
  CB := L.nCB
  cs := L.ncs
  cst := fun c => (0, L.sys.cst c)
  top := fun x => L.sys.top x * x
  cb_cst := ncb_cst
  cb_iff := ncb_iff
  val_cst := fun c x => by simp [nval, L.sys.val_cst]
  cb_cstI := fun c x h => ⟨lt_of_le_of_lt zero_le h, L.sys.cb_cstI c x h⟩
  lt_top := fun l hl hl1 p hCB => nlt_top_E (ups_inE hl) (ups_lt_Om1 l hl1) p hCB
  one_le_top := fun l hl hl1 => by
    have hρE := ups_inE hl
    exact (one_le_iff_pos.2 hρE.pos).trans (le_mul_right _ (T_pos hρE (ups_lt_Om1 l hl1)))
  rep := fun l hl hl1 v hv => by
    have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    have hT0 : L.sys.top (upsilon l) ≠ 0 := (T_pos hρE hρ1).ne'
    have hq : v / L.sys.top (upsilon l) < upsilon l := (Ordinal.lt_mul_iff_div_lt hT0).1 hv
    obtain ⟨t, ht, et⟩ := L.sys.rep l hl hl1 _ (mod_lt v hT0)
    refine ⟨(v / L.sys.top (upsilon l), t), ⟨hq, ht⟩, ?_⟩
    show L.sys.top (upsilon l) * (v / L.sys.top (upsilon l)) + L.sys.val t (upsilon l) = v
    rw [et]; exact div_add_mod v _
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (ntop_lt_ups (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1))).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun l hl hl1 p hCB h1 R => npkg hl hl1 p hCB h1 R
  rs := fun l hl hl1 p hCB => nrs hl hl1 p hCB
  uni_le := fun σ ρ hσ hρ hB p q hp hq => by
    have hσ1 := hB.2.2.1.trans hB.2.2.2
    have hpρ : L.sys.CB p.2 ρ := L.sys.cb_iff p.2 σ ρ hp.2
      (fun c hc => (L.sys.cb_cst p.2 σ hp.2 c hc).trans hB.2.2.1)
    have hqρ : L.sys.CB q.2 ρ := L.sys.cb_iff q.2 σ ρ hq.2
      (fun c hc => (L.sys.cb_cst q.2 σ hq.2 c hc).trans hB.2.2.1)
    show L.sys.top ρ * p.1 + L.sys.val p.2 ρ ≤ L.sys.top ρ * q.1 + L.sys.val q.2 ρ ↔
      L.sys.top σ * p.1 + L.sys.val p.2 σ ≤ L.sys.top σ * q.1 + L.sys.val q.2 σ
    rw [xt1_lex_le (L.lt_top_E ρ hB.2.1 hB.2.2.2 _ hpρ) (L.lt_top_E ρ hB.2.1 hB.2.2.2 _ hqρ),
      xt1_lex_le (L.lt_top_E σ hB.1 hσ1 _ hp.2) (L.lt_top_E σ hB.1 hσ1 _ hq.2),
      L.sys.uni_le σ ρ hσ hρ hB p.2 q.2 hp.2 hq.2]
  small := nsmall

/-- **The witness pair of the new top `T(ρ)·ρ`.** -/
theorem ntop_wit {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ L.sys.top ρ * ρ ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        (∃ e', f (L.sys.top ρ * ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧
          L.sys.top (f ρ) * f ρ ≤ f (L.sys.top ρ * ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  have hρδ := h.ρδ
  have hρr : ω ^ ρ = ρ := hρE
  obtain ⟨Wt, Zt, hwt, htW, hIt⟩ := L.top_wit ρ τ δ h
  set T := L.sys.top ρ with hT
  have hTe : T = ω ^ L.E ρ := L.top_eq ρ hρE hρ1
  have hρT : ρ < T := L.top_gt ρ hρE hρ1
  have hTδ : T < δ := L.top_lt_ups ρ δ hρE hρ1 hρδ h.next.2.1
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hpe : T * ρ = ω ^ (L.E ρ + ρ) := by rw [hTe, opow_add, hρr]
  have hpδ : T * ρ < δ := h.δE.mul_lt hTδ hρδ
  have hTp : T < T * ρ := lt_mul_of_one_lt_right (hρE.pos.trans hρT) h1ρ
  have hρp : ρ < T * ρ := hρT.trans hTp
  have hpρδ : T * ρ + ρ < δ := hδI.add_lt hpδ hρδ
  have hw : WZ ρ δ (insert (T * ρ + ρ) (insert (T * ρ) (insert ρ Wt))) Zt := by
    have w0 := hwt.insW le_rfl hρδ (Or.inl (inE_indec hρE))
    have w1 := w0.insW hρp.le hpδ (Or.inl (by rw [hpe]; exact indec_opow _))
    exact w1.insW (hρp.le.trans le_self_add) hpρδ
      (Or.inr ⟨T * ρ, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
        hρp.trans_le le_self_add, rfl⟩)
  refine ⟨_, _, hw, by simp, fun A f hW hZ C => ?_⟩
  have hpA : T * ρ ∈ A := hW (by simp)
  have hpρA : T * ρ + ρ ∈ A := hW (by simp)
  have hTA : T ∈ A := hW (by simp [htW])
  have hρA : ρ ∈ A := C.rho
  obtain ⟨⟨e', hfe', hdv⟩, hle⟩ :=
    hIt A f (fun x hx => hW (by simp [Finset.mem_coe.1 hx])) hZ C
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρr : ω ^ f ρ = f ρ := hfρE
  have hfTp : f T < f (T * ρ) := C.mono hTA hpA hTp
  have hfρT : f ρ ≤ f T := C.mono.monotoneOn hρA hTA hρT.le
  have hfρp : f ρ < f (T * ρ) := hfρT.trans_lt hfTp
  have hsrc : le1 (T * ρ) (T * ρ + ρ) := by
    have hne : L.E ρ + ρ ≠ 0 := (lt_of_lt_of_le hρE.pos le_add_self).ne'
    refine (h.lowδ _ _ hρp hpρδ.le).2 ?_
    refine (le1R_thm22 hρE.pos hρp.le).2 ⟨L.E ρ + ρ, hne, hpe, ?_⟩
    refine (le_lg_iff hne ρ).2 ?_
    exact dvd_add (L.exp_dvd ρ hρE hρ1) ⟨1, by rw [mul_one, hρr]⟩
  have himg : le1 (f (T * ρ)) (f (T * ρ) + f ρ) := by
    have := C.cov1 _ hpA _ hpρA hsrc
    rwa [← C.add _ hpA ρ hρA _ hpρA rfl] at this
  have key : (∃ a, f (T * ρ) = ω ^ a ∧ ω ^ f ρ ∣ a) ∧ f T * f ρ ≤ f (T * ρ) := by
    by_cases hU : UpsPt (f (T * ρ))
    · have hE := upsPt_inE hU
      exact ⟨⟨f (T * ρ), hE.symm, opow_dvd_of_inE hE hfρp.le⟩, (hE.mul_lt hfTp hfρp).le⟩
    · have hR := (C.sk _ (C.low _ hpA) hU _).1 himg
      obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfρE.pos hfρp.le).1 hR
      have hdiv : ω ^ f ρ ∣ a := (le_lg_iff ha0 _).1 hza
      have h3 : e' < a := by
        have := hfTp; rw [hfa, hfe'] at this
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      have h5 := dvd_next hdiv hdv h3
      rw [hfρr] at h5
      refine ⟨⟨a, hfa, hdiv⟩, ?_⟩
      calc f T * f ρ = ω ^ e' * ω ^ f ρ := by rw [hfe', hfρr]
        _ = ω ^ (e' + f ρ) := (opow_add ω e' (f ρ)).symm
        _ ≤ ω ^ a := opow_le_opow_right omega0_pos h5
        _ = f (T * ρ) := hfa.symm
  exact ⟨key.1, (mul_le_mul_left hle _).trans key.2⟩

/-- **The next layer**: the terms `T(x)·γ + s(x)`, top `T(x)·x = ω^{E(x)+x}`. -/
noncomputable def xtNext (L : XtLay) : XtLay where
  sys := nsys L
  E := fun x => L.E x + x
  top_eq := fun x hx hx1 => by
    show L.sys.top x * x = ω ^ (L.E x + x)
    rw [L.top_eq x hx hx1, opow_add, show ω ^ x = x from hx]
  exp_dvd := fun x hx hx1 => dvd_add (L.exp_dvd x hx hx1) ⟨1, by rw [mul_one]; exact hx.symm⟩
  exp_lt := fun x hx hx1 => Om1_add_lt (L.exp_lt x hx hx1) hx1
  top_gt := fun x hx hx1 =>
    (L.top_gt x hx hx1).trans_le (le_mul_left _ hx.pos)
  top_lt_ups := fun _ _ hx hx1 hxu hu => ntop_lt_ups hx hx1 hxu hu
  lt_top_E := fun _ hx hx1 p hp => nlt_top_E hx hx1 p hp
  exact := fun _ _ hσ hρ hB p hp => nexact hσ hρ hB p hp
  exp_pi := fun σ ρ hσ hρ hB => by
    obtain ⟨h1, h2⟩ := L.exp_pi σ ρ hσ hρ hB
    obtain ⟨h3, h4⟩ := pi_base hB
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by rw [h6, h2, h4]⟩
  top_wit := fun ρ τ δ h => ntop_wit h

end XtLay

/-- **The `n`-th layer**: `xtLayN 0 = vzLay`, `xtLayN (n+1) = (xtLayN n).xtNext`. -/
noncomputable def xtLayN : ℕ → XtLay
  | 0 => vzLay
  | n + 1 => (xtLayN n).xtNext

/-- **The top of the `n`-th layer is `B(x)·x^n`.** -/
theorem xtLayN_top (n : ℕ) (x : Ordinal.{0}) : (xtLayN n).sys.top x = VzB x * x ^ (n : Ordinal.{0}) := by
  induction n with
  | zero => show VzB x = _; rw [Nat.cast_zero, opow_zero, mul_one]
  | succ n ih =>
    show (xtLayN n).sys.top x * x = _
    rw [ih, Nat.cast_succ, ← succ_eq_add_one, opow_succ, mul_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Xt
