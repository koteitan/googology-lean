import Googology.Trans.PoR.InaccPsi.R2.GcFrM

/-!
# Atoms over a base: `Γ_{Ω₁+1+a}` for every `a < Z`, and `Γ_{Ω₁·2}`; the codes up to `Γ_{Ω₁·2+1}`

The atoms of `R2.GcAt` are the `Γ_{Ω₁+1+α}` with a constant `α < ε₀`.  The diagonal top `Γ_{x+x}` reads the code
`Γ_{Ω₁+1+Ω₁} = Γ_{Ω₁·2}`, and the codes below it use `Γ_{Ω₁+1+a}` with a parameter `a`; so the atoms depend on the
base `Z`: `gdAt Z = {Γ_{Ω₁+1+a} : a < Z} ∪ {Γ_{Ω₁·2}}`, and the codes over `Z` are `GxCl Z (gdAt Z)` (the generic
codes of `R2.MxGx`, whose readings `gxTh` are additive, keep `ω^·` and the φ-law for every atom set).

* `gdAt`, `gdAt_GxAt`, `gdAt_mono` (**the atoms grow with the base**), `gdV = Γ_{Ω₁+1+Ω₁+1}` (the bound);
* `gd_psi` (**`ψ_{Ω₂}(α) = Γ_{Ω₁+1+α}` for every `α ≤ Ω₁ + 1`**), `gd_D_psi` (`ψ_{Ω₂}(Ω₁) = Γ_{Ω₁·2}`);
* `gdCl_lt_V`, `gdCl_mem_CSet` (**a code over `Z` lies in every hull `Cl(a, b)` with `Ω₁ < a`, `Z ≤ b`**),
  `gdCl_of_CSet` (**the hull below `gdV` consists of codes** when every countable member of `Cl(a, Z)` is below `Z`:
  a collapse `ψ_π(e)` in `[Ω₁, gdV)` has `π = Ω₂`, `e ≤ Ω₁`, `e < Z` or `e = Ω₁`), `gdCl_mono`, `gd_support`
  (**a code over a strongly critical `Z` is a code over some `Z' < Z`**);
* `GdPoly X E` (**terms for the codes below `E`**, read at every strongly critical base above the code's base).

No new axiom.  New definitions: `gdAt`, `gdV`, `GdPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc

/-- **The atoms over `Z`**: `Γ_{Ω₁+1+a}` for `a < Z`, and `Γ_{Ω₁+1+Ω₁} = Γ_{Ω₁·2}`. -/
def gdAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ a, (a < Z ∨ a = Om 1) ∧ s = gcG a}

/-- **The bound**: `Γ_{Ω₁+1+Ω₁+1}`. -/
noncomputable def gdV : Ordinal.{0} := gcG (Om 1 + 1)

theorem gdAt_GxAt (Z : Ordinal.{0}) : GxAt (gdAt Z) := by
  rintro s ⟨a, -, rfl⟩
  exact ⟨gcG_SC a, gcG_Om1_lt a⟩

theorem gdAt_mono {Z Z' : Ordinal.{0}} (h : Z ≤ Z') : gdAt Z ⊆ gdAt Z' := by
  rintro s ⟨a, ha, rfl⟩
  exact ⟨a, ha.imp (fun h' => h'.trans_le h) id, rfl⟩

theorem gdCl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (gdAt Z) c) : GxCl Z' (gdAt Z') c :=
  hc.mono h (gdAt_mono h)

theorem gdG_atom {Z a : Ordinal.{0}} (ha : a < Z) : gcG a ∈ gdAt Z := ⟨a, Or.inl ha, rfl⟩

theorem gdD_atom (Z : Ordinal.{0}) : gcG (Om 1) ∈ gdAt Z := ⟨Om 1, Or.inr rfl, rfl⟩

theorem gdAt_le {Z s : Ordinal.{0}} (hZ : Z ≤ Om 1) (hs : s ∈ gdAt Z) : s ≤ gcG (Om 1) := by
  obtain ⟨a, ha, rfl⟩ := hs
  rcases ha with ha | rfl
  · exact gcG_le (ha.le.trans hZ)
  · exact le_rfl

theorem gdV_SC : SC gdV := gcG_SC _

theorem gdD_lt_V : gcG (Om 1) < gdV := gcG_lt (lt_add_one _)

theorem gdAt_lt_V {Z s : Ordinal.{0}} (hZ : Z ≤ Om 1) (hs : s ∈ gdAt Z) : s < gdV :=
  (gdAt_le hZ hs).trans_lt gdD_lt_V

/-- **A code over `Z ≤ Ω₁` is below `gdV`.** -/
theorem gdCl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (gdAt Z) c) : c < gdV := by
  have hSC := gdV_SC
  induction hc with
  | small h => exact (h.trans_le hZ).trans (gcG_Om1_lt _)
  | om => exact gcG_Om1_lt _
  | atom hs => exact gdAt_lt_V hZ hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

variable {S : InaccSeq.{0}}

theorem gd_le_Om1_mem {α β a : Ordinal.{0}} (hβ : β ≤ Om 1) :
    β ∈ S.CSet a (S.psi α (Om (1 + 1))) := by
  rcases hβ.lt_or_eq with h | rfl
  · exact CSet.of_lt (h.trans (ga_Om1_lt_psi α))
  · exact CSet.Om_mem (CSet.one_mem _ _)

/-- **`ψ_{Ω₂}(α) = Γ_{Ω₁+1+α}`** for every `α ≤ Ω₁ + 1`. -/
theorem gd_psi (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, α ≤ Om 1 + 1 → S.psi α (Om (1 + 1)) = gcG α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  refine le_antisymm (gaPsi_le S (gcG_SC α) (gcG_Om1_lt α) fun e he => ?_)
    (gcG_le_of (ga_psi_SC α) (ga_Om1_lt_psi α) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hα)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hα)]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) hβ
      (gd_le_Om1_mem (Order.lt_add_one_iff.1 (hβ.trans_le hα)))

theorem gd_D_psi (S : InaccSeq.{0}) : S.psi (Om 1) (Om (1 + 1)) = gcG (Om 1) := gd_psi S _ le_self_add

theorem gdV_psi (S : InaccSeq.{0}) : S.psi (Om 1 + 1) (Om (1 + 1)) = gdV := gd_psi S _ le_rfl

theorem gdV_lt_Om2 (S : InaccSeq.{0}) : gdV < Om (1 + 1) := by
  rw [← gdV_psi S]; exact psi_lt (InR_Om_succ 1) _

theorem gdAt_param {Z s : Ordinal.{0}} (hZ : Z ≤ Om 1) (hs : s ∈ gdAt Z) :
    ∃ α, α ≤ Om 1 ∧ (α < Z ∨ α = Om 1) ∧ s = gcG α := by
  obtain ⟨α, hα, rfl⟩ := hs
  refine ⟨α, ?_, hα, rfl⟩
  rcases hα with h | rfl
  · exact (h.trans_le hZ).le
  · exact le_rfl

/-- An atom lies in every hull `Cl(a, b)` with `Ω₁ < a` and `Z ≤ b`. -/
theorem gdAt_mem {Z a b s : Ordinal.{0}} (hZ : Z ≤ Om 1) (ha : Om 1 < a) (hZb : Z ≤ b) (hs : s ∈ gdAt Z) :
    s ∈ S.CSet a b := by
  obtain ⟨α, hαΩ, hα, rfl⟩ := gdAt_param hZ hs
  rw [← gd_psi S α (hαΩ.trans le_self_add)]
  have hαC : α ∈ S.CSet a b := by
    rcases hα with h | rfl
    · exact CSet.of_lt (h.trans_le hZb)
    · exact CSet.Om_mem (CSet.one_mem _ _)
  exact CSet.psi_mem (hαΩ.trans_lt ha) (InR_Om_succ 1) (ga_Om2_mem _ _) hαC

/-- **A code over `Z ≤ Ω₁` lies in every hull `Cl(a, b)` with `Ω₁ < a` and `Z ≤ b`.** -/
theorem gdCl_mem_CSet {Z a b : Ordinal.{0}} (hZ : Z ≤ Om 1) (ha : Om 1 < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z (gdAt Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gdAt_mem hZ ha hZb hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `gdV` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every member of
`Cl(a, Z)` below `gdV` is a code over `Z`. -/
theorem gdCl_of_CSet {Z a : Ordinal.{0}} (hZ : 0 < Z) (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < gdV → GxCl Z (gdAt Z) x := by
  intro x hx
  have hx' := hx
  have hG2 := (gdV_lt_Om2 S).le
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | zero => exact fun _ => GxCl.zero hZ
  | inacc n =>
    intro h
    exact absurd ((h.trans_le hG2).trans (mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro h
    exact absurd ((h.trans_le hG2).trans mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le hG2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hZ
    · rw [h1]; exact GxCl.om
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)
    rcases eq_or_ne s 0 with rfl | hs0
    · have hlt : S.psi e.1 (Om (0 + 1)) < Om 1 := by
        have := psi_lt (InR_Om_succ (S := S) 0) e.1
        rwa [zero_add] at this ⊢
      exact GxCl.small (hkey _ hx' hlt)
    rcases eq_or_ne s 1 with rfl | hs1
    · -- `x = ψ_{Ω₂}(e)` with `e ≤ Ω₁`
      have heΩ : e.1 ≤ Om 1 := by
        by_contra hgt
        push Not at hgt
        have h3 : Om 1 + 1 ≤ e.1 := Order.add_one_le_of_lt hgt
        rcases h3.lt_or_eq with h4 | h4
        · have h5 := psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) h4
            (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _)))
          rw [gdV_psi S] at h5
          exact absurd (h5.trans h) (lt_irrefl _)
        · have h5 : S.psi e.1 (Om (1 + 1)) = gdV := by rw [← h4]; exact gdV_psi S
          exact absurd h (by rw [h5]; exact lt_irrefl _)
      rw [gd_psi S e.1 (heΩ.trans le_self_add)]
      rcases heΩ.lt_or_eq with he | he
      · exact GxCl.atom (gdG_atom (hkey _ he1 he))
      · rw [he]; exact GxCl.atom (gdD_atom Z)
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`** (the parameters of its atoms included). -/
theorem gd_support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (gdAt Z) x) :
    ∃ Z' < Z, GxCl Z' (gdAt Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨a, ha, rfl⟩ := hs
    rcases ha with ha | rfl
    · exact ⟨a + 1, hZ.isPrincipal ha h1, GxCl.atom (gdG_atom (lt_add_one a))⟩
    · exact ⟨0, hZ.1, GxCl.atom (gdD_atom 0)⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (gdCl_mono (le_max_left _ _) g1) (gdCl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (gdCl_mono (le_max_left _ _) g1) (gdCl_mono (le_max_right _ _) g2)⟩

theorem gd_Om1_lt_A (η : Ordinal.{0}) : Om 1 < ConjT.Aη S η := by
  have h1 : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  exact h1.trans_le le_self_add

theorem gd_Om1_lt_A1 (η : Ordinal.{0}) : Om 1 < ConjT.Aη S η + 1 := (gd_Om1_lt_A η).trans_le le_self_add

/-- **Terms for the codes below `E`** (atoms over the base): for every code `c < E` over `Z` some term of `X` has the
value `Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GdPoly (X : Xt.XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (gdAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (gdAt y) c

end Googology.Trans.PoR.InaccPsi.R2.Gd
