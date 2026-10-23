import Googology.Trans.PoR.InaccPsi.R2.LpTm

/-!
# Layers valid only above a constant: the gated systems, the gated layers, the gated ladder terms

A layer whose top carries a constant `ν` (for example `Γ_{x+1+ν} = ϑˣ(Ω₁·Ω₁ + ν)` with `ν` not below every
`ε`-number) exists only at the bases `x > ν`: Lemma EXACT for its top fails across `ν` (`π_{σ,ρ}(Γ_{ρ+1+ν})` is not
defined for `σ ≤ ν < ρ`).  Here every field of a term system and of a layer is asked only at the bases above a fixed
**gate** `g`:

* `GdSys g` (`R2.XtSys` with every base `x`, restart `υ_λ`, pair of bases `σ < ρ` above `g`), `GdLay g` (`R2.XtLay`
  likewise; the top witness is asked for the copies that keep `g`, `GdCtx`), `GdB` (**the gated base package**: a
  gate `g`, a gated layer `K`, `E_K(x) ∈ E ∩ Tˣ` above `g`); `GdSys.ofXt`, `GdLay.ofXt`, `GdB.ofLp` (every ungated
  object is gated at every gate), `GdLay.mono`, `GdB.mono` (a gate can be raised);
* `GdCtx g ρ A f` (**a covering copy that keeps the gate**: `g ∈ A`, so `g < f(ρ)` when `g < ρ`);
* `GdX B` (the exponent terms over `K`: terms of `K`, `E_K`, sums, powers; `R2.LxTm` above the gate), `gdxt_pi`
  (EXACT), `gdxt_rep` (representation below `ε_{E_K(ρ)+1}`), `gdxt_img` (**Lemma IMG below `ε_{E_K(ρ)+1}`**);
* `GdT B` (**the ladder terms over the gated base**: `R2.LpTm` above the gate), `gdP` (the stage tops), `GdT.gd_TB`,
  `gd_quot`, `gd_rep` (every ordinal below `gdP B n x` is a value of stage `≤ n`), `GdT.pi` (**EXACT above the
  gate**), `GdT.uni_le`, `gd_small`.

No new axiom.  New definitions: `GdSys`, `GdLay`, `GdB`, `GdCtx`, `GdX`, `GdT` and their functions.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly

/-! ## The gated structures -/

/-- **A term system above the gate `g`**: the fields of `R2.XtSys`, each asked only at bases above `g`. -/
structure GdSys (g : Ordinal.{0}) where
  Tm : Type 1
  val : Tm → Ordinal.{0} → Ordinal.{0}
  CB : Tm → Ordinal.{0} → Prop
  cs : Tm → List Ordinal.{0}
  cst : Ordinal.{0} → Tm
  top : Ordinal.{0} → Ordinal.{0}
  cb_cst : ∀ t s, CB t s → ∀ c ∈ cs t, c < s
  cb_iff : ∀ t s s', CB t s → (∀ c ∈ cs t, c < s') → CB t s'
  val_cst : ∀ c x, val (cst c) x = c
  cb_cstI : ∀ c x, c < x → CB (cst c) x
  lt_top : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → ∀ t, CB t (upsilon l) →
    val t (upsilon l) < top (upsilon l)
  one_le_top : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → 1 ≤ top (upsilon l)
  rep : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → ∀ v < top (upsilon l), ∃ t, CB t (upsilon l) ∧
    val t (upsilon l) = v
  top_lt : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → top (upsilon l) < upsilon (l + ω + 1)
  pkg : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → ∀ t, CB t (upsilon l) → 1 ≤ val t (upsilon l) →
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val t)
  rs : ∀ l, IsRestartIdx l → l < Om1 → g < upsilon l → ∀ t, CB t (upsilon l) → RsStep l (val t)
  uni_le : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → ∀ t u, CB t σ → CB u σ →
    (val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ)
  small : ∀ t, (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → g < x → CB t x → x ≤ val t x)

/-- **A covering copy that keeps the gate**: `g ∈ A`. -/
structure GdCtx (g ρ : Ordinal.{0}) (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Prop
    extends ImgCtx ρ A f where
  gate : g ∈ A

theorem GdCtx.lt {g ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : GdCtx g ρ A f)
    (hg : g < ρ) : g < f ρ := C.above g C.gate hg

/-- **A layer above the gate `g`**: the fields of `R2.XtLay`, each asked only at bases above `g`; the top witness for
the copies that keep `g`. -/
structure GdLay (g : Ordinal.{0}) where
  sys : GdSys g
  E : Ordinal.{0} → Ordinal.{0}
  top_eq : ∀ x, InE x → x < Om1 → g < x → sys.top x = ω ^ E x
  exp_dvd : ∀ x, InE x → x < Om1 → g < x → ω ^ x ∣ E x
  exp_lt : ∀ x, InE x → x < Om1 → g < x → E x < Om1
  top_gt : ∀ x, InE x → x < Om1 → g < x → x < sys.top x
  top_lt_ups : ∀ x u, InE x → x < Om1 → g < x → x < u → UpsPt u → sys.top x < u
  lt_top_E : ∀ x, InE x → x < Om1 → g < x → ∀ t, sys.CB t x → sys.val t x < sys.top x
  exact : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → ∀ t, sys.CB t σ →
    sys.val t ρ ∈ TB ρ σ ∧ pi σ ρ (sys.val t ρ) = sys.val t σ
  exp_pi : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → E ρ ∈ TB ρ σ ∧ pi σ ρ (E ρ) = E σ
  top_wit : ∀ ρ τ δ, RstK ρ τ δ → g < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ sys.top ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx g ρ A f →
      (∃ e', f (sys.top ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ sys.top (f ρ) ≤ f (sys.top ρ)

/-- **The gated base package**: a gate, a gated layer, its top exponent an `ε`-number in `Tˣ` above the gate. -/
structure GdB where
  g : Ordinal.{0}
  K : GdLay g
  ek : ∀ x, InE x → x < Om1 → g < x → InE (K.E x)
  mem : ∀ x, InE x → x < Om1 → g < x → K.E x ∈ Tset x

/-! ## Ungated objects are gated; raising the gate -/

/-- An ungated term system, gated at `g`. -/
def GdSys.ofXt (X : XtSys) (g : Ordinal.{0}) : GdSys g where
  Tm := X.Tm
  val := X.val
  CB := X.CB
  cs := X.cs
  cst := X.cst
  top := X.top
  cb_cst := X.cb_cst
  cb_iff := X.cb_iff
  val_cst := X.val_cst
  cb_cstI := X.cb_cstI
  lt_top := fun l hl hl1 _ => X.lt_top l hl hl1
  one_le_top := fun l hl hl1 _ => X.one_le_top l hl hl1
  rep := fun l hl hl1 _ => X.rep l hl hl1
  top_lt := fun l hl hl1 _ => X.top_lt l hl hl1
  pkg := fun l hl hl1 _ => X.pkg l hl hl1
  rs := fun l hl hl1 _ => X.rs l hl hl1
  uni_le := fun σ ρ hσ hρ hB _ => X.uni_le σ ρ hσ hρ hB
  small := fun t => (X.small t).imp id fun h x hx hx1 _ => h x hx hx1

/-- An ungated layer, gated at `g`. -/
def GdLay.ofXt (L : XtLay) (g : Ordinal.{0}) : GdLay g where
  sys := GdSys.ofXt L.sys g
  E := L.E
  top_eq := fun x hx hx1 _ => L.top_eq x hx hx1
  exp_dvd := fun x hx hx1 _ => L.exp_dvd x hx hx1
  exp_lt := fun x hx hx1 _ => L.exp_lt x hx hx1
  top_gt := fun x hx hx1 _ => L.top_gt x hx hx1
  top_lt_ups := fun x u hx hx1 _ => L.top_lt_ups x u hx hx1
  lt_top_E := fun x hx hx1 _ => L.lt_top_E x hx hx1
  exact := fun σ ρ hσ hρ hB _ => L.exact σ ρ hσ hρ hB
  exp_pi := fun σ ρ hσ hρ hB _ => L.exp_pi σ ρ hσ hρ hB
  top_wit := fun ρ τ δ h _ => by
    obtain ⟨W, Z, hw, hm, hI⟩ := L.top_wit ρ τ δ h
    exact ⟨W, Z, hw, hm, fun A f hW hZ C => hI A f hW hZ C.1⟩

/-- An ungated base package, gated at `g`. -/
def GdB.ofLp (B : Lp.LpB) (g : Ordinal.{0}) : GdB where
  g := g
  K := GdLay.ofXt B.K g
  ek := fun x hx hx1 _ => B.ek x hx hx1
  mem := fun x hx hx1 _ => B.mem x hx hx1

/-- **Raising the gate** of a term system. -/
def GdSys.mono {g g' : Ordinal.{0}} (X : GdSys g) (h : g ≤ g') : GdSys g' where
  Tm := X.Tm
  val := X.val
  CB := X.CB
  cs := X.cs
  cst := X.cst
  top := X.top
  cb_cst := X.cb_cst
  cb_iff := X.cb_iff
  val_cst := X.val_cst
  cb_cstI := X.cb_cstI
  lt_top := fun l hl hl1 hg => X.lt_top l hl hl1 (h.trans_lt hg)
  one_le_top := fun l hl hl1 hg => X.one_le_top l hl hl1 (h.trans_lt hg)
  rep := fun l hl hl1 hg => X.rep l hl hl1 (h.trans_lt hg)
  top_lt := fun l hl hl1 hg => X.top_lt l hl hl1 (h.trans_lt hg)
  pkg := fun l hl hl1 hg => X.pkg l hl hl1 (h.trans_lt hg)
  rs := fun l hl hl1 hg => X.rs l hl hl1 (h.trans_lt hg)
  uni_le := fun σ ρ hσ hρ hB hg => X.uni_le σ ρ hσ hρ hB (h.trans_lt hg)
  small := fun t => (X.small t).imp id fun h' x hx hx1 hg => h' x hx hx1 (h.trans_lt hg)

/-- **Raising the gate** of a layer (the top witness is asked for copies that keep the new gate; the old gate
`g ≤ g' < ρ` is kept by them too). -/
def GdLay.mono {g g' : Ordinal.{0}} (L : GdLay g) (h : g ≤ g') : GdLay g' where
  sys := L.sys.mono h
  E := L.E
  top_eq := fun x hx hx1 hg => L.top_eq x hx hx1 (h.trans_lt hg)
  exp_dvd := fun x hx hx1 hg => L.exp_dvd x hx hx1 (h.trans_lt hg)
  exp_lt := fun x hx hx1 hg => L.exp_lt x hx hx1 (h.trans_lt hg)
  top_gt := fun x hx hx1 hg => L.top_gt x hx hx1 (h.trans_lt hg)
  top_lt_ups := fun x u hx hx1 hg => L.top_lt_ups x u hx hx1 (h.trans_lt hg)
  lt_top_E := fun x hx hx1 hg => L.lt_top_E x hx hx1 (h.trans_lt hg)
  exact := fun σ ρ hσ hρ hB hg => L.exact σ ρ hσ hρ hB (h.trans_lt hg)
  exp_pi := fun σ ρ hσ hρ hB hg => L.exp_pi σ ρ hσ hρ hB (h.trans_lt hg)
  top_wit := fun ρ τ δ hR hg => by
    classical
    obtain ⟨W, Z, hw, hm, hI⟩ := L.top_wit ρ τ δ hR (h.trans_lt hg)
    refine ⟨W, insert g Z, hw.insZ (h.trans_lt hg), hm, fun A f hW hZ C => ?_⟩
    have hgA : g ∈ A := hZ (by simp)
    exact hI A f hW (fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx))))
      ⟨C.1, hgA⟩

/-- **Raising the gate** of a base package. -/
def GdB.mono (B : GdB) {g' : Ordinal.{0}} (h : B.g ≤ g') : GdB where
  g := g'
  K := B.K.mono h
  ek := fun x hx hx1 hg => B.ek x hx hx1 (h.trans_lt hg)
  mem := fun x hx hx1 hg => B.mem x hx hx1 (h.trans_lt hg)

/-! ## The exponent terms over a gated layer (`R2.LxTm` above the gate) -/

/-- **The exponent terms over the gated layer**: terms of `K`, the atom `E_K(x)`, sums and `ω`-powers. -/
inductive GdX (B : GdB) : Type 1
  | bs : B.K.sys.Tm → GdX B
  | tp : GdX B
  | sm : GdX B → GdX B → GdX B
  | pw : GdX B → GdX B

namespace GdX

variable {B : GdB}

/-- The value at the base `x`. -/
noncomputable def val : GdX B → Ordinal.{0} → Ordinal.{0}
  | bs t, x => B.K.sys.val t x
  | tp, x => B.K.E x
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`. -/
def CBt : GdX B → Ordinal.{0} → Prop
  | bs t, s => B.K.sys.CB t s
  | tp, _ => True
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : GdX B → List Ordinal.{0}
  | bs t => B.K.sys.cs t
  | tp => []
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_bs (t : B.K.sys.Tm) (x : Ordinal.{0}) : val (bs t) x = B.K.sys.val t x := rfl
@[simp] theorem val_tp (x : Ordinal.{0}) : val (tp : GdX B) x = B.K.E x := rfl
@[simp] theorem val_sm (a b : GdX B) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : GdX B) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : GdX B) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | bs t, s, s', h, h' => B.K.sys.cb_iff t s s' h h'
  | tp, _, _, _, _ => trivial
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : GdX B) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | bs t, s, h, c, hc => B.K.sys.cb_cst t s h c hc
  | tp, _, _, c, hc => by simp [cs] at hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : GdX B} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end GdX

open GdX

variable {B : GdB}

/-- The constants of the constant term `0` of a gated term system are `0`. -/
theorem gdx_cs_cst0 {g : Ordinal.{0}} (X : GdSys g) : ∀ c ∈ X.cs (X.cst 0), c = 0 := fun c hc =>
  Order.lt_one_iff.1 (X.cb_cst _ 1 (X.cb_cstI 0 1 zero_lt_one) c hc)

section Base

/-- The top of `K` is `E_K(x)`. -/
theorem gdx_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) : B.K.sys.top x = B.K.E x := by
  rw [B.K.top_eq x hx hx1 hg]; exact B.ek x hx hx1 hg

theorem gdx_E_gt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) : x < B.K.E x := by
  rw [← gdx_top hx hx1 hg]; exact B.K.top_gt x hx hx1 hg

/-- **`ε_{E_K(x)+1}` lies below `Ω₁` and below every `υ`-point above `x`.** -/
theorem gdx_eN_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    eN (B.K.E x) < Om1 ∧ ∀ u, x < u → UpsPt u → eN (B.K.E x) < u := by
  have hb := ly_eN_lt (B.ek x hx hx1 hg) (B.K.exp_lt x hx hx1 hg)
  exact ⟨hb.1, fun u hxu hu => hb.2 u (by rw [← gdx_top hx hx1 hg]; exact B.K.top_lt_ups x u hx hx1 hg hxu hu)
    hu.2⟩

/-- **Every value is below `ε_{E_K(x)+1}`.** -/
theorem gdxt_lt_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ t : GdX B, CBt t x → val t x < eN (B.K.E x)
  | bs t, h => by
    rw [val_bs, ← gdx_top hx hx1 hg]; exact (B.K.lt_top_E x hx hx1 hg t h).trans (lt_eN _)
  | tp, _ => lt_eN _
  | sm a b, h => (inE_indec (eN_E _)).add_lt (gdxt_lt_eN hx hx1 hg a h.1) (gdxt_lt_eN hx hx1 hg b h.2)
  | pw a, h => (eN_E _).opow_lt (gdxt_lt_eN hx hx1 hg a h)

theorem gdxt_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) (t : GdX B) (h : CBt t x) :
    val t x < Om1 :=
  (gdxt_lt_eN hx hx1 hg t h).trans (gdx_eN_lt hx hx1 hg).1

/-- **Lemma EXACT for `GdX B`** above the gate. -/
theorem gdxt_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ) :
    ∀ t : GdX B, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | bs t, h => B.K.exact σ ρ hσ hρ hB hg t h
  | tp, _ => B.K.exp_pi σ ρ hσ hρ hB hg
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := gdxt_pi hσ hρ hB hg a h.1
    obtain ⟨h3, h4⟩ := gdxt_pi hσ hρ hB hg b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := gdxt_pi hσ hρ hB hg a h
    have hb := gdxt_lt_Om1 hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1) a (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem gdxt_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ)
    {t u : GdX B} (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := gdxt_pi hσ hρ hB hg t ht
  obtain ⟨h3, h4⟩ := gdxt_pi hσ hρ hB hg u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem gdxt_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ)
    {t u : GdX B} (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, gdxt_uni_le hσ hρ hB hg ht hu, gdxt_uni_le hσ hρ hB hg hu ht]

/-- **A value `0` is the value `0` everywhere.** -/
theorem gdxt_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ t : GdX B, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | bs t, h, h0 => by
    rcases B.K.sys.small t with hc | hc
    · intro y; rw [val_bs, hc y x]; exact h0
    · have := hc x hx hx1 hg h
      rw [val_bs] at h0; rw [h0] at this
      exact absurd this (not_le.2 hx.pos)
  | tp, _, h0 => absurd h0 (B.ek x hx hx1 hg).pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, gdxt_zero hx hx1 hg a h.1 this.1 y, gdxt_zero hx hx1 hg b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Base

/-- An `ε`-number strictly between `E_K(x)` and `ε_{E_K(x)+1}` does not exist. -/
theorem gdx_no_eps {x e : Ordinal.{0}} (hBe : B.K.E x < e) (he : e < eN (B.K.E x)) : ¬ InE e :=
  fun hE => absurd (eN_le hBe hE) (not_le.2 he)

/-! ### Representation -/

/-- Every value below `E_K(ρ)` is the value of a term of `K`. -/
def GdXRep (B : GdB) (ρ : Ordinal.{0}) : Prop :=
  ∀ v < B.K.E ρ, ∃ t : B.K.sys.Tm, B.K.sys.CB t ρ ∧ B.K.sys.val t ρ = v

theorem gdxRep_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hg : B.g < upsilon l) :
    GdXRep B (upsilon l) := fun v hv =>
  B.K.sys.rep l hl hl1 hg v (by rw [gdx_top (ups_inE hl) (ups_lt_Om1 l hl1) hg]; exact hv)

/-- **Representation below `ε_{E_K(ρ)+1}`.** -/
theorem gdxt_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) (hr : GdXRep B ρ) :
    ∀ v, v < eN (B.K.E ρ) → ∃ t : GdX B, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (B.K.E ρ) with hvB | rfl | hBv
  · obtain ⟨t, ht, htv⟩ := hr v hvB
    exact ⟨bs t, ht, htv⟩
  · exact ⟨tp, trivial, rfl⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0 | h0
  · rw [h0, zero_add] at hvs
    have hzv : lg v < v := by
      have hz : lg v ≤ ω ^ lg v := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz.trans_eq hvs.symm) fun e => ?_
      exact gdx_no_eps hBv hv (show ω ^ v = v from
        calc ω ^ v = ω ^ lg v := by rw [e]
          _ = v := hvs.symm)
    obtain ⟨t, ht, htv⟩ := IH _ hzv (hzv.trans hv)
    exact ⟨pw t, ht, by rw [val_pw, htv, ← hvs]⟩
  · have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0 hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨t1, ht1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨t2, ht2, hv2⟩ := IH _ hwv (hwv.trans hv)
    exact ⟨sm t1 t2, ⟨ht1, ht2⟩, by rw [val_sm, hv1, hv2, ← hvs]⟩

/-! ### Lemma IMG below `ε_{E_K(ρ)+1}` -/

variable {ρ τ δ : Ordinal.{0}}

/-- **The IMG statement for one value** `v` with a term `t` of `GdX B`, for the copies that keep the gate. -/
def GdXImg (B : GdB) (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : GdX B) : Prop :=
  WZ ρ δ W Z ∧ CBt t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ val t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx B.g ρ A f →
      val t (f ρ) ≤ f v

/-- **The IMG statement below `E_K(ρ)`**. -/
def GdXBase (B : GdB) (ρ δ : Ordinal.{0}) : Prop :=
  ∀ v < B.K.E ρ, ∃ W Z : Finset Ordinal.{0}, ∃ t : GdX B, GdXImg B ρ δ v W Z t

/-- **`GdXBase` holds at every restart above the gate**: the IMG package of the term of `K`. -/
theorem gdxBase_ri {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hg : B.g < upsilon l)
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    GdXBase B (upsilon l) (upsilon (l + ω + 1)) := by
  classical
  intro v hv
  have hρE := R.ρE
  have hρ1 := R.ρ1
  rcases eq_or_ne v 0 with rfl | h0
  · refine ⟨∅, insert 0 ∅, bs (B.K.sys.cst 0), WZ.empty.insZ hρE.pos, B.K.sys.cb_cstI 0 _ hρE.pos,
      fun c hc => by rw [gdx_cs_cst0 B.K.sys c hc]; exact Finset.mem_insert_self _ _, by
        rw [val_bs, B.K.sys.val_cst], by simp, fun A f _ _ _ => by rw [val_bs, B.K.sys.val_cst]; exact zero_le⟩
  · obtain ⟨t, ht, hvt⟩ := B.K.sys.rep l hl hl1 hg v (by rw [gdx_top hρE hρ1 hg]; exact hv)
    obtain ⟨-, -, W, Z, hw, hm, hI⟩ :=
      B.K.sys.pkg l hl hl1 hg t ht (by rw [hvt]; exact one_le_iff_ne_zero.2 h0) R
    have hwc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (B.K.sys.cs t).toFinset :=
      ⟨by simp, fun z hz => B.K.sys.cb_cst t _ ht z (List.mem_toFinset.1 hz), by simp⟩
    have hw2 := hw.union hwc
    rw [Finset.union_empty] at hw2
    refine ⟨W, Z ∪ (B.K.sys.cs t).toFinset, bs t, hw2, ht,
      fun c hc => Finset.mem_union_right _ (List.mem_toFinset.2 hc), hvt, ?_, fun A f hW hZ C => ?_⟩
    · rw [← hvt]
      rcases Finset.mem_union.1 hm with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    · rw [val_bs, ← hvt]
      exact hI A f hW (fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))) C.1

theorem gdxt_cbt_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : GdX B}
    (ht : CBt t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CBt t (f ρ) :=
  cbt_iff t ρ (f ρ) ht (fun c hc => C.above c (hA c hc) (cbt_cst t ρ ht c hc))

theorem gdxt_val_fρ (h : RstK ρ τ δ) (hg : B.g < ρ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : GdCtx B.g ρ A f) {t u : GdX B} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A)
    (huA : ∀ c ∈ cs u, c ∈ A) (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (gdxt_uni_eq C.ups h.ρU (h.img_bases C.1) (C.lt hg) (gdxt_cbt_img C.1 ht htA)
    (gdxt_cbt_img C.1 hu huA)).1 htu

theorem gdxImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : GdX B} (hI : GdXImg B ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `ε_{E_K(ρ)+1}`** (above the gate). -/
theorem gdxt_img (h : RstK ρ τ δ) (hg : B.g < ρ) (hb : GdXBase B ρ δ) :
    ∀ v, v < eN (B.K.E ρ) → ∃ W Z t, GdXImg B ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hBE := B.ek ρ hρE hρ1 hg
  have hρB : ρ < B.K.E ρ := gdx_E_gt hρE hρ1 hg
  have heδ : eN (B.K.E ρ) ≤ δ := ((gdx_eN_lt hρE hρ1 hg).2 δ h.ρδ h.next.2.1).le
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans_le heδ
  rcases lt_trichotomy v (B.K.E ρ) with hvB | rfl | hBv
  · exact hb v hvB
  · obtain ⟨W, Z, hw, hTW, hI⟩ := B.K.top_wit ρ τ δ h hg
    rw [gdx_top hρE hρ1 hg] at hTW
    refine ⟨W, Z, tp, hw, trivial, by simp [cs], rfl, Finset.mem_union_left _ hTW, fun A f hW hZ C => ?_⟩
    have h2 := (hI A f hW hZ C).2
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans hρ1
    rw [gdx_top hfE hf1 (C.lt hg), gdx_top hρE hρ1 hg] at h2
    exact h2
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0 | h0
  · -- `v = ω^z`, `z = z' + ω^q`
    rw [h0, zero_add] at hvs
    set z := lg v with hz
    have hzv : z < v := by
      have hz' : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz'.trans_eq hvs.symm) fun e => ?_
      exact gdx_no_eps hBv hv (show ω ^ v = v from
        calc ω ^ v = ω ^ z := by rw [e]
          _ = v := hvs.symm)
    have hz0 : z ≠ 0 := by
      intro e; rw [e, opow_zero] at hvs
      exact absurd (hvs ▸ hBv) (not_lt.2 (one_le_iff_pos.2 hBE.pos))
    obtain ⟨z', hzs, -, hz'z⟩ := lg_split hz0
    set q := lg z with hq
    have hqz : q ≤ z := lg_le hz0
    have hqv : q < v := hqz.trans_lt hzv
    have hPv : ω ^ z' < v := by
      rw [hvs]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hz'z
    obtain ⟨Wq, Zq, tq, Iq⟩ := IH q hqv (hqv.trans hv)
    obtain ⟨Wp, Zp, tp', Ip⟩ := IH _ hPv (hPv.trans hv)
    obtain ⟨Wz, Zz, tz, Iz⟩ := IH z' (hz'z.trans hzv) ((hz'z.trans hzv).trans hv)
    set t := pw (sm tz (pw tq)) with ht
    have htv : val t ρ = v := by
      rw [ht, val_pw, val_sm, val_pw, Iz.2.2.2.1, Iq.2.2.2.1, ← hzs, ← hvs]
    have hw0 : WZ ρ δ ((Wq ∪ Wp) ∪ Wz) ((Zq ∪ Zp) ∪ Zz) := (Iq.1.union Ip.1).union Iz.1
    have hcsT : ∀ c ∈ cs t, c ∈ (Zq ∪ Zp) ∪ Zz := by
      intro c hc
      simp only [ht, cs, List.mem_append] at hc
      rcases hc with hc | hc
      · simp [Iz.2.2.1 c hc]
      · simp [Iq.2.2.1 c hc]
    have hcbT : CBt t ρ := ⟨Iz.2.1, Iq.2.1⟩
    have hmem : ∀ {x W Z}, x ∈ W ∪ Z → W ⊆ (Wq ∪ Wp) ∪ Wz → Z ⊆ (Zq ∪ Zp) ∪ Zz →
        x ∈ ((Wq ∪ Wp) ∪ Wz) ∪ ((Zq ∪ Zp) ∪ Zz) := fun hx hW hZ =>
      Finset.union_subset_union hW hZ hx
    have hPW0 := hmem Ip.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    have hqW0 := hmem Iq.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    have hcom : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑((Wq ∪ Wp) ∪ Wz) ⊆ A →
        ↑((Zq ∪ Zp) ∪ Zz) ⊆ A → GdCtx B.g ρ A f → val tq (f ρ) ≤ f q ∧
          ∀ e1, f (ω ^ z') = ω ^ e1 → val tz (f ρ) ≤ e1 := by
      intro A f hW hZ C
      have hWq : ↑Wq ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZq : ↑Zq ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hWp : ↑Wp ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZp : ↑Zp ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZz : ↑Zz ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      refine ⟨Iq.2.2.2.2.2 A f hWq hZq C, fun e1 he1 => ?_⟩
      have hpA := (gdxImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := gdxt_val_fρ h hg C (t := pw tz) (u := tp') Iz.2.1 Ip.2.1 hzA hpA
        (by rw [val_pw, Iz.2.2.2.1, Ip.2.2.2.1])
      have hle := Ip.2.2.2.2.2 A f hWp hZp C
      rw [← heq, val_pw, he1] at hle
      exact (opow_le_opow_iff_right one_lt_omega0).1 hle
    rcases eq_or_ne q 0 with hq0 | hq0
    · have hw : WZ ρ δ (insert v ((Wq ∪ Wp) ∪ Wz)) ((Zq ∪ Zp) ∪ Zz) :=
        hw0.insW hρv.le hvδ (Or.inl (hvs ▸ indec_opow _))
      refine ⟨_, _, t, hw, hcbT, hcsT, htv, by simp, fun A f hW hZ C => ?_⟩
      have hW0 : ↑((Wq ∪ Wp) ∪ Wz) ⊆ A := fun x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      obtain ⟨hqf, hzf⟩ := hcom A f hW0 hZ C
      have hvA : v ∈ A := hW (by simp)
      have hPA : ω ^ z' ∈ A := mem_A hPW0 hW0 hZ
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec v hvA (hvs ▸ indec_opow _))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      have h2 : f (ω ^ z') < f v := C.mono hPA hvA hPv
      rw [hc, he1] at h2
      have h3 : e1 < c := (opow_lt_opow_iff_right one_lt_omega0).1 h2
      have htq0 : val tq (f ρ) = 0 :=
        gdxt_zero hρE hρ1 hg tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
      rw [hc, ht, val_pw, val_sm, val_pw, htq0, opow_zero]
      exact opow_le_opow_right omega0_pos ((add_le_add (hzf e1 he1) le_rfl).trans (Order.add_one_le_of_lt h3))
    · have hNe : v = ω ^ (z' + ω ^ q) := by rw [hvs, hzs]
      obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ := lyStep2 h (hNe ▸ hρv) (pos_iff_ne_zero.2 hq0)
        (hNe ▸ hqv) (hNe ▸ hvδ) hw0 hPW0 hqW0
      refine ⟨W, Z, t, hw, hcbT, fun c hc => hZZ (hcsT c hc), htv, Finset.mem_union_left _ (hNe ▸ hNW),
        fun A f hW hZ C => ?_⟩
      obtain ⟨hqf, hzf⟩ := hcom A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx)))
        (fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))) C
      obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ C.1
      have hPA : ω ^ z' ∈ A := by
        rcases Finset.mem_union.1 hPW0 with h' | h'
        · exact hW (Finset.mem_coe.2 (hWW h'))
        · exact hZ (Finset.mem_coe.2 (hZZ h'))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      rw [hNe, ha, ht, val_pw, val_sm, val_pw]
      exact opow_le_opow_right omega0_pos
        ((add_le_add (hzf e1 he1) (opow_le_opow_right omega0_pos hqf)).trans (hnext e1 he1))
  · -- `v = v' + ω^{lg v}`, `v' ≠ 0`: a sum
    have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0 hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨W1, Z1, t1, I1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨W2, Z2, t2, I2⟩ := IH _ hwv (hwv.trans hv)
    have hw : WZ ρ δ (insert v (W1 ∪ W2)) (Z1 ∪ Z2) := by
      refine (I1.1.union I2.1).insW hρv.le hvδ (Or.inr ⟨v', ?_, ω ^ lg v, ?_, hv'v, hwv, hvs.symm⟩)
      · exact Finset.union_subset_union (Finset.subset_union_left) (Finset.subset_union_left) I1.2.2.2.2.1
      · exact Finset.union_subset_union (Finset.subset_union_right) (Finset.subset_union_right) I2.2.2.2.2.1
    refine ⟨_, _, sm t1 t2, hw, ⟨I1.2.1, I2.2.1⟩, fun c hc => ?_, by rw [val_sm, I1.2.2.2.1, I2.2.2.2.1, ← hvs],
      by simp, fun A f hW hZ C => ?_⟩
    · simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (I1.2.2.1 c hc)
      · exact Finset.mem_union_right _ (I2.2.2.1 c hc)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have h1A := (gdxImg_sub I1 hW1 hZ1).2
    have h2A := (gdxImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)

/-! ## The ladder terms over a gated base (`R2.LpTm` above the gate) -/

/-- **The tops over the gated base**: `gdP 0 x = E_K(x)`, `gdP (n+1) x = ϑˣ(Ω₁·gdP n x)`. -/
noncomputable def gdP (B : GdB) : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, x => B.K.E x
  | n + 1, x => vt x (Om1 * gdP B n x)

/-- **The terms over the gated base layer.** -/
inductive GdT (B : GdB) : Type 1
  | cst : Ordinal.{0} → GdT B
  | bs : GdT B
  | ak : B.K.sys.Tm → GdT B
  | tp : GdT B
  | th0 : Ordinal.{0} → GdT B → GdT B
  | tl : GdT B → GdT B → GdT B
  | sm : GdT B → GdT B → GdT B
  | pw : GdT B → GdT B

namespace GdT

variable {B : GdB}

/-- The value at the base `x`. -/
noncomputable def val : GdT B → Ordinal.{0} → Ordinal.{0}
  | cst a, _ => a
  | bs, x => x
  | ak k, x => B.K.sys.val k x
  | tp, x => B.K.E x
  | th0 b t, x => vt x (Om1 * b + val t x)
  | tl l t, x => vt x (Om1 * val l x + val t x)
  | sm a b, x => val a x + val b x
  | pw t, x => ω ^ val t x

/-- The constants. -/
def cs : GdT B → List Ordinal.{0}
  | cst a => [a]
  | bs => []
  | ak k => B.K.sys.cs k
  | tp => []
  | th0 b t => b :: cs t
  | tl l t => cs l ++ cs t
  | sm a b => cs a ++ cs b
  | pw t => cs t

/-- Base-free: built from constants and constant terms of `K` by sums and powers. -/
def noB : GdT B → Prop
  | cst _ => True
  | bs => False
  | ak k => ∀ y z, B.K.sys.val k y = B.K.sys.val k z
  | tp => False
  | th0 _ _ => False
  | tl _ _ => False
  | sm a b => noB a ∧ noB b
  | pw t => noB t

/-- The side condition: constants below the base, constant levels at least `1`, level terms not base-free. -/
def CBt : GdT B → Ordinal.{0} → Prop
  | cst a, x => a < x
  | bs, _ => True
  | ak k, x => B.K.sys.CB k x
  | tp, _ => True
  | th0 b t, x => 1 ≤ b ∧ b < x ∧ CBt t x
  | tl l t, x => ¬ noB l ∧ CBt l x ∧ CBt t x
  | sm a b, x => CBt a x ∧ CBt b x
  | pw t, x => CBt t x

/-- The stage: the nesting depth of the levels (`tp` has stage `1`). -/
def stage : GdT B → ℕ
  | cst _ => 0
  | bs => 0
  | ak _ => 0
  | tp => 1
  | th0 _ t => max 1 (stage t)
  | tl l t => max (stage l + 1) (stage t)
  | sm a b => max (stage a) (stage b)
  | pw t => stage t

@[simp] theorem val_cst (a x : Ordinal.{0}) : val (cst a : GdT B) x = a := rfl
@[simp] theorem val_bs (x : Ordinal.{0}) : val (bs : GdT B) x = x := rfl
@[simp] theorem val_ak (k : B.K.sys.Tm) (x : Ordinal.{0}) : val (ak k) x = B.K.sys.val k x := rfl
@[simp] theorem val_tp (x : Ordinal.{0}) : val (tp : GdT B) x = B.K.E x := rfl
@[simp] theorem val_th0 (b : Ordinal.{0}) (t : GdT B) (x : Ordinal.{0}) :
    val (th0 b t) x = vt x (Om1 * b + val t x) := rfl
@[simp] theorem val_tl (l t : GdT B) (x : Ordinal.{0}) :
    val (tl l t) x = vt x (Om1 * val l x + val t x) := rfl
@[simp] theorem val_sm (a b : GdT B) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (t : GdT B) (x : Ordinal.{0}) : val (pw t) x = ω ^ val t x := rfl

/-- A base-free term has constant value. -/
theorem noB_val : ∀ t : GdT B, noB t → ∀ x y, val t x = val t y
  | .cst _, _, _, _ => rfl
  | .bs, h, _, _ => absurd h id
  | .ak k, h, x, y => h x y
  | .tp, h, _, _ => absurd h id
  | .th0 _ _, h, _, _ => absurd h id
  | .tl _ _, h, _, _ => absurd h id
  | .sm a b, h, x, y => by simp only [val_sm, noB_val a h.1 x y, noB_val b h.2 x y]
  | .pw t, h, x, y => by simp only [val_pw, noB_val t h x y]

/-- The side condition depends only on the listed constants. -/
theorem cbt_iff {t : GdT B} {x y : Ordinal.{0}} (h : CBt t x)
    (hy : ∀ c ∈ cs t, c < y) : CBt t y := by
  induction t with
  | cst a => exact hy a (by simp [cs])
  | bs => trivial
  | ak k => exact B.K.sys.cb_iff k x y h hy
  | tp => trivial
  | th0 b t ih =>
      refine ⟨h.1, hy b (by simp [cs]), ?_⟩
      exact ih h.2.2 (fun c hc => hy c (by simp [cs, hc]))
  | tl l t ihl iht =>
      exact ⟨h.1, ihl h.2.1 (fun c hc => hy c (by simp [cs, hc])),
        iht h.2.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | sm a b iha ihb =>
      exact ⟨iha h.1 (fun c hc => hy c (by simp [cs, hc])),
        ihb h.2 (fun c hc => hy c (by simp [cs, hc]))⟩
  | pw t ih => exact ih h (fun c hc => hy c (by simpa [cs] using hc))

/-- All explicit constants and level parameters are below the base. -/
theorem cbt_cst {ρ : Ordinal.{0}} {s : GdT B} (hs : CBt s ρ) : ∀ c ∈ cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [cs] at hc
  | ak k => exact B.K.sys.cb_cst k ρ hs
  | tp => intro c hc; simp [cs] at hc
  | th0 b t ih =>
      intro c hc
      simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.2.1
      · exact ih hs.2.2 c hc
  | tl l t ihl iht =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihl hs.2.1 c hc
      · exact iht hs.2.2 c hc
  | sm a b iha ihb =>
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hs.1 c hc
      · exact ihb hs.2 c hc
  | pw t ih => intro c hc; exact ih hs c (by simpa [cs] using hc)

/-- The side condition is monotone in the base. -/
theorem CBt.mono {s : GdT B} {x y : Ordinal.{0}} (hxy : x ≤ y) (hs : CBt s x) : CBt s y :=
  cbt_iff hs (fun c hc => (cbt_cst hs c hc).trans_le hxy)

/-- **At a `υ`-point above the gate a constant term of `K` has value below the base.** -/
theorem ak_const_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) (hg : B.g < x) {k : B.K.sys.Tm}
    (hn : ∀ y z, B.K.sys.val k y = B.K.sys.val k z) (hk : B.K.sys.CB k x) : B.K.sys.val k x < x := by
  have hxE := upsPt_inE hx
  set C := B.K.sys.val k x with hC
  have hC1 : C < Om1 := by
    have h1 := B.K.lt_top_E x hxE hx1 hg k hk
    rw [gdx_top hxE hx1 hg] at h1
    exact h1.trans (B.K.exp_lt x hxE hx1 hg)
  have h11 : (1 : Ordinal.{0}) < Om1 := lt_of_le_of_lt (one_le_iff_pos.2 hxE.pos) hx1
  have hlt : x + C + 1 < Om1 := Om1_add_lt (Om1_add_lt hx1 hC1) h11
  have hpos : 0 < x + C + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  have hU := upsPt_upsilon hpos
  have hU1 : upsilon (x + C + 1) < Om1 := ups_lt_Om1 _ hlt
  have hle : x + C + 1 ≤ upsilon (x + C + 1) := upsilon_normal.strictMono.le_apply
  have hxu : x < upsilon (x + C + 1) :=
    lt_of_le_of_lt le_self_add (lt_of_lt_of_le (lt_add_one (x + C)) hle)
  have hCu : C < upsilon (x + C + 1) :=
    lt_of_le_of_lt le_add_self (lt_of_lt_of_le (lt_add_one (x + C)) hle)
  have hB : Bases x (upsilon (x + C + 1)) := ⟨hxE, upsPt_inE hU, hxu, hU1⟩
  have hex := (B.K.exact x _ hx hU hB hg k hk).1
  rw [hn (upsilon (x + C + 1)) x] at hex
  exact (TB_inter_lt hB hCu).1 hex

/-- A base-free term with constants below a `υ`-point `x` above the gate has value below `x`. -/
theorem noB_lt {x : Ordinal.{0}} (hx : UpsPt x) (hx1 : x < Om1) (hg : B.g < x) :
    ∀ t : GdT B, noB t → CBt t x → val t x < x
  | .cst _, _, h => h
  | .bs, h, _ => absurd h id
  | .ak _, hn, h => ak_const_lt hx hx1 hg hn h
  | .tp, h, _ => absurd h id
  | .th0 _ _, h, _ => absurd h id
  | .tl _ _, h, _ => absurd h id
  | .sm a b, hn, h =>
      (inE_indec (upsPt_inE hx)).add_lt (noB_lt hx hx1 hg a hn.1 h.1) (noB_lt hx hx1 hg b hn.2 h.2)
  | .pw t, hn, h => (upsPt_inE hx).opow_lt (noB_lt hx hx1 hg t hn h)

end GdT

/-- The term of the top `gdP n`: `gdTm 0 = tp`, `gdTm (n+1) = ϑ(Ω₁·gdTm n + 0)`. -/
def gdTm {B : GdB} : ℕ → GdT B
  | 0 => .tp
  | n + 1 => .tl (gdTm n) (.cst 0)

theorem gdTm_stage {B : GdB} : ∀ n : ℕ, GdT.stage (gdTm n : GdT B) = n + 1
  | 0 => rfl
  | n + 1 => by
      show max (GdT.stage (gdTm n : GdT B) + 1) 0 = n + 1 + 1
      rw [gdTm_stage n]; simp

section Base

variable (B : GdB) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x)
include hx hx1 hg

/-- The facts on the tops. -/
theorem gdP_facts : ∀ n : ℕ, gdP B n x ∈ Tset x ∧ x < gdP B n x ∧ gdP B n x < Om1 ∧ InE (gdP B n x)
  | 0 => ⟨B.mem x hx hx1 hg, gdx_E_gt hx hx1 hg, B.K.exp_lt x hx hx1 hg, B.ek x hx hx1 hg⟩
  | n + 1 => by
      obtain ⟨hT, hxg, hg1, -⟩ := gdP_facts n
      obtain ⟨-, -, c, d, e, f, -, -, -⟩ :=
        Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)
      simp only [add_zero] at c d e f
      exact ⟨c, d, e, f⟩

theorem gdP_lt_succ (n : ℕ) : gdP B n x < gdP B (n + 1) x := by
  obtain ⟨hT, hxg, hg1, -⟩ := gdP_facts B hx hx1 hg n
  have := (Lv.gen_facts hx hx1 hT hxg.le hg1 (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1)).2.2.2.2.2.2.2.1
  simpa using this

theorem gdP_mono {m n : ℕ} (h : m ≤ n) : gdP B m x ≤ gdP B n x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (gdP_lt_succ B hx hx1 hg _).le

/-- Below the top of the next stage: `ϑˣ(Ω₁·β + η) < gdP (m+1) x`. -/
theorem gd_lt_top {m : ℕ} {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβ : β < gdP B m x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : η < gdP B (m + 1) x) : vt x (Om1 * β + η) < gdP B (m + 1) x := by
  obtain ⟨hgT, hxg, hg1, -⟩ := gdP_facts B hx hx1 hg m
  have hgt : gdP B m x < gdP B (m + 1) x := gdP_lt_succ B hx hx1 hg m
  have e : gdP B (m + 1) x = vt x (Om1 * gdP B m x + 0) := by rw [add_zero]; rfl
  rw [e] at h hgt ⊢
  refine lvVt_lt_gen hx hx1 hβT (hβ.trans hg1) hgT hxg.le hg1 hη hη1
    (mem_T_of_le hx hx1 zero_le) (Ordinal.omega_pos 1) ?_ (hβ.trans hgt) h
  rw [add_zero]
  calc Om1 * β + η < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hη1
    _ = Om1 * (β + 1) := by rw [mul_add_one]
    _ ≤ Om1 * gdP B m x := mul_le_mul_right (add_one_le_of_lt hβ) Om1

end Base

namespace GdT

variable {B : GdB}

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x)
include hx hx1 hg

/-- **A term denotes a member of `Tˣ` below the top of its stage** (above the gate), and a term that is not
base-free has value at least the base. -/
theorem gd_TB : ∀ t : GdT B, CBt t x →
    (val t x ∈ Tset x ∧ val t x < gdP B (stage t) x) ∧ (¬ noB t → x ≤ val t x)
  | .cst a, h => by
      obtain ⟨hT, hxg, hg1, -⟩ := gdP_facts B hx hx1 hg 0
      exact ⟨⟨vz_T_down hx hx1 hT hg1 (h.trans hxg).le, h.trans hxg⟩, fun hn => absurd trivial hn⟩
  | .bs, _ => ⟨⟨mem_T_of_le hx hx1 le_rfl, (gdP_facts B hx hx1 hg 0).2.1⟩, fun _ => le_rfl⟩
  | .ak k, h => by
      obtain ⟨hT, -, hg1, -⟩ := gdP_facts B hx hx1 hg 0
      have hlt : B.K.sys.val k x < B.K.E x := by
        have := B.K.lt_top_E x hx hx1 hg k h
        rwa [gdx_top hx hx1 hg] at this
      refine ⟨⟨vz_T_down hx hx1 hT hg1 hlt.le, hlt⟩, fun hn => ?_⟩
      rcases B.K.sys.small k with hc | hc
      · exact absurd hc hn
      · exact hc x hx hx1 hg h
  | .tp, _ => by
      obtain ⟨hT, hxg, hg1, -⟩ := gdP_facts B hx hx1 hg 0
      exact ⟨⟨hT, gdP_lt_succ B hx hx1 hg 0⟩, fun _ => hxg.le⟩
  | .th0 b t, h => by
      obtain ⟨⟨htT, htLt⟩, -⟩ := gd_TB t h.2.2
      have hst : stage t ≤ max 1 (stage t) := le_max_right _ _
      obtain ⟨m, hm⟩ : ∃ m, max 1 (stage t) = m + 1 := ⟨max 1 (stage t) - 1, by omega⟩
      have ht' : val t x < gdP B (m + 1) x := htLt.trans_le (gdP_mono B hx hx1 hg (hm ▸ hst))
      have ht1 : val t x < Om1 := ht'.trans (gdP_facts B hx hx1 hg _).2.2.1
      have hargT := Lu.luOm1_mul_add_T hx hx1 h.2.1.le htT
      have harg2 := Lu.luOm1_mul_lt (h.2.1.trans hx1) ht1
      have hb : b < gdP B m x := h.2.1.trans (gdP_facts B hx hx1 hg m).2.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 hargT harg2
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * b + val t x) < gdP B (max 1 (stage t)) x
      rw [hm]
      exact gd_lt_top B hx hx1 hg (mem_T_of_le hx hx1 h.2.1.le) hb htT ht1 ht'
  | .tl l t, h => by
      obtain ⟨⟨hlT, hlLt⟩, hlx⟩ := gd_TB l h.2.1
      obtain ⟨⟨htT, htLt⟩, -⟩ := gd_TB t h.2.2
      obtain ⟨m, hm'⟩ : ∃ m, max (stage l + 1) (stage t) = m + 1 :=
        ⟨max (stage l + 1) (stage t) - 1, by omega⟩
      have hlm : stage l ≤ m := by omega
      have htm : stage t ≤ m + 1 := by omega
      have hl' : val l x < gdP B m x := hlLt.trans_le (gdP_mono B hx hx1 hg hlm)
      have ht' : val t x < gdP B (m + 1) x := htLt.trans_le (gdP_mono B hx hx1 hg htm)
      have hl1 : val l x < Om1 := hl'.trans (gdP_facts B hx hx1 hg m).2.2.1
      have ht1 : val t x < Om1 := ht'.trans (gdP_facts B hx hx1 hg _).2.2.1
      have hxl : x ≤ val l x := hlx h.1
      obtain ⟨hvT, hxv, -⟩ := vt_memTwo hx hx1 (lvArg_mem hx hx1 hlT hxl hl1 htT ht1) (Lu.luOm1_mul_lt hl1 ht1)
      refine ⟨⟨hvT, ?_⟩, fun _ => hxv⟩
      show vt x (Om1 * val l x + val t x) < gdP B (max (stage l + 1) (stage t)) x
      rw [hm']
      exact gd_lt_top B hx hx1 hg hlT hl' htT ht1 ht'
  | .sm a b, h => by
      obtain ⟨⟨haT, haLt⟩, hax⟩ := gd_TB a h.1
      obtain ⟨⟨hbT, hbLt⟩, hbx⟩ := gd_TB b h.2
      have hE := (gdP_facts B hx hx1 hg (max (stage a) (stage b))).2.2.2
      refine ⟨⟨vzT_add hx hx1 haT hbT, (inE_indec hE).add_lt
        (haLt.trans_le (gdP_mono B hx hx1 hg (le_max_left _ _)))
        (hbLt.trans_le (gdP_mono B hx hx1 hg (le_max_right _ _)))⟩, fun hn => ?_⟩
      simp only [noB, not_and_or] at hn
      rcases hn with hn | hn
      · exact (hax hn).trans le_self_add
      · exact (hbx hn).trans le_add_self
  | .pw t, h => by
      obtain ⟨⟨htT, htLt⟩, htx⟩ := gd_TB t h
      obtain ⟨hgT, -, hg1, hgE⟩ := gdP_facts B hx hx1 hg (stage t)
      have hw : ω ^ val t x < gdP B (stage t) x := hgE.opow_lt htLt
      exact ⟨⟨vz_T_down hx hx1 hgT hg1 hw.le, hw⟩, fun hn => (htx hn).trans (right_le_opow _ one_lt_omega0)⟩

theorem gd_T (t : GdT B) (h : CBt t x) : val t x ∈ Tset x ∧ val t x < gdP B (stage t) x :=
  (gd_TB hx hx1 hg t h).1

theorem le_of_not_noB (t : GdT B) (h : CBt t x) (hn : ¬ noB t) : x ≤ val t x :=
  (gd_TB hx hx1 hg t h).2 hn

theorem gd_lt_Om1 (t : GdT B) (h : CBt t x) : val t x < Om1 :=
  (gd_T hx hx1 hg t h).2.trans (gdP_facts B hx hx1 hg _).2.2.1

end Base

end GdT

section Base2

variable {B : GdB} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x)
include hx hx1 hg

omit hx1 hg in
theorem gdTm_val : ∀ n : ℕ, GdT.CBt (gdTm n : GdT B) x ∧ GdT.val (gdTm n : GdT B) x = gdP B n x
  | 0 => ⟨trivial, rfl⟩
  | n + 1 => by
      obtain ⟨hc, hv⟩ := gdTm_val n
      refine ⟨⟨?_, hc, hx.pos⟩, ?_⟩
      · cases n <;> exact id
      · show vt x (Om1 * GdT.val (gdTm n : GdT B) x + 0) = gdP B (n + 1) x
        rw [hv, add_zero]; rfl

/-- **An `ε`-number above `E_K(x)` and below `gdP (m+1) x` has an argument quotient below `gdP m x`.** -/
theorem gd_quot : ∀ m : ℕ, ∀ ξ, ξ ∈ Tset x → ξ < OmTwo → x < vt x ξ → InE (vt x ξ) →
    B.K.E x < vt x ξ → vt x ξ < gdP B (m + 1) x → ξ / Om1 < gdP B m x := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have h1x : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have h1T : (1 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h1x.le
  have h11 : (1 : Ordinal.{0}) < Om1 := h1x.trans hx1
  intro m
  induction m with
  | zero =>
    intro ξ hξT hξ2 hxξ hE hEξ h
    obtain ⟨hgT, hxg, hg1, -⟩ := gdP_facts B hx hx1 hg 0
    have hlt : gdP B 0 x < vt x ξ := hEξ
    have := lvLt_of_vt_lt hx hx1 hξT hξ2 hgT hxg.le hg1 h0T (Ordinal.omega_pos 1)
      (hx.pos.trans hxξ) hlt (by rw [add_zero]; exact h)
    have h1 : Om1 * (ξ / Om1) < Om1 * gdP B 0 x :=
      lt_of_le_of_lt (mul_div_le ξ Om1) (by simpa using this)
    exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
  | succ k ih =>
    intro ξ hξT hξ2 hxξ hE hEξ h
    obtain ⟨hgT, hxg, hg1, hgE⟩ := gdP_facts B hx hx1 hg (k + 1)
    rcases lt_trichotomy (gdP B (k + 1) x) (vt x ξ) with hlt | heq | hgt
    · have := lvLt_of_vt_lt hx hx1 hξT hξ2 hgT hxg.le hg1 h0T (Ordinal.omega_pos 1)
        (hx.pos.trans hxξ) hlt (by rw [add_zero]; exact h)
      have h1 : Om1 * (ξ / Om1) < Om1 * gdP B (k + 1) x :=
        lt_of_le_of_lt (mul_div_le ξ Om1) (by simpa using this)
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1
    · obtain ⟨hkT, hxk, hk1, -⟩ := gdP_facts B hx hx1 hg k
      have hk : gdP B k x < gdP B (k + 1) x := gdP_lt_succ B hx hx1 hg k
      have h2 : vt x (Om1 * gdP B k x + 0) < vt x (Om1 * gdP B k x + 1) :=
        lvVt_eta_lt hx hx1 hkT hxk.le hk1 h0T (Ordinal.omega_pos 1) h1T h11 zero_lt_one
          (hx.pos.trans (Lv.gen_facts hx hx1 hkT hxk.le hk1 h1T h11).2.2.2.1)
      have h3 : ξ < Om1 * gdP B k x + 1 :=
        lvLt_of_vt_lt hx hx1 hξT hξ2 hkT hxk.le hk1 h1T h11 (by rw [← heq]; exact Lu.lu_one_lt_E hgE)
          (by rw [← heq]; exact hk) (by rw [← heq]; simpa using h2)
      have h4 : Om1 * (ξ / Om1) < Om1 * (gdP B k x + 1) := by
        calc Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
          _ < Om1 * gdP B k x + 1 := h3
          _ ≤ Om1 * gdP B k x + Om1 := add_le_add_right h11.le _
          _ = Om1 * (gdP B k x + 1) := by rw [mul_add_one]
      have h5 : ξ / Om1 < gdP B k x + 1 := (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h4
      exact (Order.lt_add_one_iff.1 h5).trans_lt hk
    · exact (ih ξ hξT hξ2 hxξ hE hEξ hgt).trans (gdP_lt_succ B hx hx1 hg k)

end Base2

/-- Every value below `E_K(x)` is a value of `K` (at `x`). -/
theorem gd_rep0 {B : GdB} {x : Ordinal.{0}} (hr : GdXRep B x) :
    ∀ v, v < B.K.E x → ∃ t : GdT B, GdT.CBt t x ∧ GdT.stage t ≤ 0 ∧ GdT.val t x = v := fun v hv => by
  obtain ⟨k, hk, hkv⟩ := hr v hv
  exact ⟨.ak k, hk, le_rfl, hkv⟩

/-- **Every ordinal below `gdP n x` is the value of a term of stage `≤ n`**, at a `υ`-point `x` above the gate where
every value below `E_K(x)` is a value of `K`. -/
theorem gd_rep {B : GdB} {x : Ordinal.{0}} (hxU : UpsPt x) (hx1 : x < Om1) (hg : B.g < x) (hr : GdXRep B x) :
    ∀ n : ℕ, ∀ v, v < gdP B n x → ∃ t : GdT B, GdT.CBt t x ∧ GdT.stage t ≤ n ∧ GdT.val t x = v := by
  have hx := upsPt_inE hxU
  intro n
  induction n with
  | zero => exact gd_rep0 hr
  | succ m ihm =>
    obtain ⟨hgT, -, hg1, -⟩ := gdP_facts B hx hx1 hg (m + 1)
    obtain ⟨hmT, -, hm1, -⟩ := gdP_facts B hx hx1 hg m
    have hxE := gdx_E_gt hx hx1 hg
    intro v
    induction v using WellFoundedLT.induction with
    | ind v IH =>
    intro hv
    have hv1 : v < Om1 := hv.trans hg1
    have hvT : v ∈ Tset x := vz_T_down hx hx1 hgT hg1 hv.le
    rcases lt_trichotomy v (B.K.E x) with hvE | rfl | hEv
    · obtain ⟨t, ht, hs, he⟩ := gd_rep0 hr v hvE
      exact ⟨t, ht, hs.trans (Nat.zero_le _), he⟩
    · exact ⟨.tp, trivial, by simp [GdT.stage], rfl⟩
    have hxv : x ≤ v := (hxE.trans hEv).le
    by_cases hI : Indec v
    · by_cases hE : InE v
      · have hxv' : x < v := hxE.trans hEv
        obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hvT hxv hv1 (inE_indec hE)
        have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxv', by rw [hξv]; exact hE⟩
        obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hx hx1 hξT hξ2 hΩξ
        have hqm : ξ / Om1 < gdP B m x :=
          gd_quot hx hx1 hg m ξ hξT hξ2 (by rw [hξv]; exact hxv') (by rw [hξv]; exact hE)
            (by rw [hξv]; exact hEv) (by rw [hξv]; exact hv)
        rcases lt_or_ge (ξ / Om1) x with hqx | hqx
        · have hrv : ξ % Om1 < v := by
            have h := luLt_vt_self hx hx1 hq1 hqx hrT hr1
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          exact ⟨.th0 (ξ / Om1) t, ⟨hq1, hqx, ht⟩, by simp only [GdT.stage]; omega,
            by rw [GdT.val_th0, he, hdec, hξv]⟩
        · obtain ⟨l, hlc, hls, hle⟩ := ihm (ξ / Om1) hqm
          have hqT : ξ / Om1 ∈ Tset x := vz_T_down hx hx1 hmT hm1 hqm.le
          have hrv : ξ % Om1 < v := by
            have h := (lvLevel_lt_vt hx hx1 hqT hqx (hqm.trans hm1) hrT hr1).2
            rwa [hdec, hξv] at h
          obtain ⟨t, ht, hst, he⟩ := IH _ hrv (hrv.trans hv)
          have hlB : ¬ GdT.noB l := fun hn =>
            absurd (GdT.noB_lt hxU hx1 hg l hn hlc) (not_lt.2 (hle ▸ hqx))
          exact ⟨.tl l t, ⟨hlB, hlc, ht⟩, by simp only [GdT.stage]; omega,
            by rw [GdT.val_tl, he, hle, hdec, hξv]⟩
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        have hL : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
          (fun h => hE (by unfold InE; rw [← h]; exact h.symm))
        obtain ⟨t, ht, hst, e⟩ := IH L hL (hL.trans hv)
        exact ⟨.pw t, ht, hst, by rw [GdT.val_pw, e]⟩
    · have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hx.pos hxv).ne'
      obtain ⟨s1, h1, st1, e1⟩ := IH u1 hu1 (hu1.trans hv)
      obtain ⟨s2, h2, st2, e2⟩ := IH u2 hu2 (hu2.trans hv)
      exact ⟨.sm s1 s2, ⟨h1, h2⟩, by simp only [GdT.stage]; omega, by rw [GdT.val_sm, e1, e2, hsum]⟩

namespace GdT

variable {B : GdB}

/-- The tops lie below every next point above the base. -/
theorem gd_top_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) (n : ℕ) (hxu : x < u)
    (hu : LtInf1 u) : gdP B n x < u := by
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
  obtain ⟨hT, -, htop1, -⟩ := gdP_facts B hx hx1 hg n
  exact lt_of_lt_of_le ((hTm _ htop1).1 hT) (hmin u hxu hu)

theorem gd_lt_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) {t : GdT B}
    (ht : CBt t x) (hxu : x < u) (hu : LtInf1 u) : val t x < u :=
  (gd_T hx hx1 hg t ht).2.trans (gd_top_lt_next hx hx1 hg _ hxu hu)

theorem gd_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : B.g < x) {t : GdT B}
    (ht : CBt t x) (hxu : x < u) (hu : UpsPt u) : val t x < u :=
  gd_lt_next hx hx1 hg ht hxu hu.2

/-- **Lemma EXACT** for `GdT` above the gate. -/
theorem pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ) :
    ∀ t : GdT B, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | .cst a, h => ⟨mem_TB_of_lt hB h, pi_lt hB h⟩
  | .bs, _ => pi_base hB
  | .ak k, h => B.K.exact σ ρ hσ hρ hB hg k h
  | .tp, _ => B.K.exp_pi σ ρ hσ hρ hB hg
  | .th0 b t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB hg t h.2.2
      have ht1 : val t ρ < Om1 :=
        gd_lt_Om1 hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1) t (CBt.mono hB.2.2.1.le h.2.2)
      obtain ⟨h3, h4⟩ := LvT.pi_vt_low hB h.2.1 h1 ht1
      simp only [val_th0]
      exact ⟨h3, by rw [h4, h2]⟩
  | .tl l t, h => by
      obtain ⟨hl1, hl2⟩ := pi hσ hρ hB hg l h.2.1
      obtain ⟨h1, h2⟩ := pi hσ hρ hB hg t h.2.2
      have hgρ : B.g < ρ := hg.trans hB.2.2.1
      have hcρ : CBt l ρ := CBt.mono hB.2.2.1.le h.2.1
      have hρL : ρ ≤ val l ρ := le_of_not_noB hB.2.1 hB.2.2.2 hgρ l hcρ h.1
      have hL1 : val l ρ < Om1 := gd_lt_Om1 hB.2.1 hB.2.2.2 hgρ l hcρ
      have ht1 : val t ρ < Om1 := gd_lt_Om1 hB.2.1 hB.2.2.2 hgρ t (CBt.mono hB.2.2.1.le h.2.2)
      obtain ⟨h3, h4⟩ := LvET.pi_vt_tl hB hl1 hρL hL1 h1 ht1
      simp only [val_tl]
      exact ⟨h3, by rw [h4, h2, hl2]⟩
  | .sm a b, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB hg a h.1
      obtain ⟨h3, h4⟩ := pi hσ hρ hB hg b h.2
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      simp only [val_sm]
      exact ⟨h5, by rw [h6, h2, h4]⟩
  | .pw t, h => by
      obtain ⟨h1, h2⟩ := pi hσ hρ hB hg t h
      have ht1 : val t ρ < Om1 :=
        gd_lt_Om1 hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1) t (CBt.mono hB.2.2.1.le h)
      obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 ht1
      simp only [val_pw]
      exact ⟨h3, by rw [h4, h2]⟩

/-- **Lemma EXACT** in order form. -/
theorem uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ)
    {t u : GdT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := pi hσ hρ hB hg t ht
  obtain ⟨h3, h4⟩ := pi hσ hρ hB hg u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ)
    {t u : GdT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, uni_le hσ hρ hB hg hu ht]

theorem uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) (hg : B.g < σ)
    {t u : GdT B} (ht : CBt t σ) (hu : CBt u σ) :
    val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, uni_le hσ hρ hB hg ht hu, uni_le hσ hρ hB hg hu ht]

/-- The exponent terms over `K` read as terms here. -/
def ofX : GdX B → GdT B
  | .bs t => ak t
  | .tp => tp
  | .sm a b => sm (ofX a) (ofX b)
  | .pw a => pw (ofX a)

theorem ofX_val : ∀ (t : GdX B) (x : Ordinal.{0}), val (ofX t) x = GdX.val t x
  | .bs _, _ => rfl
  | .tp, _ => rfl
  | .sm a b, x => by simp only [ofX, val_sm, GdX.val_sm, ofX_val a x, ofX_val b x]
  | .pw a, x => by simp only [ofX, val_pw, GdX.val_pw, ofX_val a x]

theorem ofX_cs : ∀ t : GdX B, cs (ofX t) = GdX.cs t
  | .bs _ => rfl
  | .tp => rfl
  | .sm a b => by simp only [ofX, cs, GdX.cs, ofX_cs a, ofX_cs b]
  | .pw a => by simp only [ofX, cs, GdX.cs, ofX_cs a]

theorem ofX_cbt : ∀ (t : GdX B) (s : Ordinal.{0}), GdX.CBt t s → CBt (ofX t) s
  | .bs _, _, h => h
  | .tp, _, _ => trivial
  | .sm a b, s, h => ⟨ofX_cbt a s h.1, ofX_cbt b s h.2⟩
  | .pw a, s, h => ofX_cbt a s h

end GdT

/-- The `small` field above the gate: a term is base-independent or at least the base. -/
theorem gd_small {B : GdB} : ∀ t : GdT B,
    (∀ x y, GdT.val t x = GdT.val t y) ∨
      (∀ x, InE x → x < Om1 → B.g < x → GdT.CBt t x → x ≤ GdT.val t x) := by
  intro t
  by_cases h : GdT.noB t
  · exact Or.inl (GdT.noB_val t h)
  · exact Or.inr (fun x hx hx1 hg hc => GdT.le_of_not_noB hx hx1 hg t hc h)

end Googology.Trans.PoR.InaccPsi.R2.Gd
