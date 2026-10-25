import Googology.Trans.PoR.InaccPsi.R2.GsRec

/-!
# (port of `R2.GmAt` to `R2.GsD` / `GsCS`: the base read only above the gate)

THE CHANGE: `GsCS` has a gate `κ < Ω₁` and asks `B ∈ C(a, b)` only for `κ < b` (`B_mem`); the hull lemma
`gsmCl_of_CSet` uses it at `b = ψ_{Ω₂}(e) > Ω₁ > κ`.  (In `R2.GmAt`, `B` is asked in every `C(a, b)`, `B < a`; for `B
= ε_{G+ν}` this needs `ν ∈ C(a, 0)`, false for large countable `ν`.)
themselves built with atoms; the hull below `Γ_{Ω₁+1+B}`

`R2.GiAt` (where `B < Γ_{Ω₁+1}`, so no code contains an atom) with the bound free: a code system `K : GsCS` is a bound
`B` with `B < Γ_{Ω₁+1+B}` and a gate `gt` on the codes `c < B` with the facts the hull calculus uses: the gate of a code
over `Z` WITH THE ATOMS OF `K` OVER `Z` is below `Z` (`code_gate`; a code `c ≥ Γ_{Ω₁+1}` contains atoms
`Γ_{Ω₁+1+c'}`, `c' < c`), a code `c` lies in every hull `Cl(a, b)` with `c < a` and its gate below `b` (`mem`), `B` in
every hull `Cl(a, b)` with `B < a`, the codes below `c` with gate below a countable base are countably many (`count`),
the gate moves by one along `+1` (`gt_succ`).  Every theorem of `R2.GiAt` holds with the same proof except where the
old proof used `B < Γ_{Ω₁+1} ≤` every atom.

* `GsCS`, `GsCS.At` (**the atoms over `Z`**: `Γ_{Ω₁+1+c}`, `c < B`, `gt c < Z`), `GsCS.V` (`Γ_{Ω₁+1+B}`);
* `gsm_psi` (**`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for every `c ≤ B`**), `gsmV_lt_Om2`, `gsmCl_mem_CSet`, `gsmCl_of_CSet` (**the
  hull
  below `Γ_{Ω₁+1+B}` consists of codes**), `gsm_support`, `gsm_B_lt_A`, `GsmPoly`.

No new axiom.  New definitions: `GsCS`, `GsCS.At`, `GsCS.V`, `GsmPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **A code system**: a bound `B` of the atom codes (`B < Γ_{Ω₁+1+B}`) and a gate `gt` with the facts of the hull
calculus; codes may contain atoms. -/
structure GsCS where
  B : Ordinal.{0}
  gt : Ordinal.{0} → Ordinal.{0}
  B_V : B < gcG B
  gt_zero : gt 0 = 0
  gt_lt : ∀ c, c < B → gt c < Om1
  gt_succ : ∀ b Z, IsSuccLimit Z → b + 1 < B → gt b < Z → gt (b + 1) < Z
  mem : ∀ (S : InaccSeq.{0}) (a b c : Ordinal.{0}), c < B → c < a → gt c < b → c ∈ S.CSet a b
  κ : Ordinal.{0}
  κ_lt : κ < Om1
  B_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), B < a → κ < b → B ∈ S.CSet a b
  code_gate : ∀ (Z : Ordinal.{0}), Z ≤ Om1 → 0 < Z →
    (∀ u v, u < Z → v < Z → u + v < Z) → (∀ u v, u < Z → v < Z → veblen u v < Z) →
    ∀ c, GxCl Z {s | ∃ c', c' < B ∧ gt c' < Z ∧ s = gcG c'} c → c < B → gt c < Z
  count : ∀ c y, c ≤ B → InE y → y < Om1 → Countable {b : Iio c // gt b.1 < y}

namespace GsCS

/-- **The atoms over `Z`**: `Γ_{Ω₁+1+c}` for every code `c < B` with `gt c < Z`. -/
def At (K : GsCS) (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ c, c < K.B ∧ K.gt c < Z ∧ s = gcG c}

/-- **The bound of the hull**: `Γ_{Ω₁+1+B}`. -/
noncomputable def V (K : GsCS) : Ordinal.{0} := gcG K.B

end GsCS

variable {K : GsCS}

theorem gsmAt_GxAt (Z : Ordinal.{0}) : GxAt (K.At Z) := by
  rintro s ⟨c, -, -, rfl⟩
  exact ⟨gcG_SC c, gcG_Om1_lt c⟩

theorem gsmAt_mono {Z Z' : Ordinal.{0}} (h : Z ≤ Z') : K.At Z ⊆ K.At Z' := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc, hg.trans_le h, rfl⟩

theorem gsmCl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (K.At Z) c) : GxCl Z' (K.At Z') c :=
  hc.mono h (gsmAt_mono h)

theorem gsmG_atom {Z c : Ordinal.{0}} (hc : c < K.B) (hg : K.gt c < Z) : gcG c ∈ K.At Z := ⟨c, hc, hg, rfl⟩

theorem gsmV_SC : SC K.V := gcG_SC _

theorem gsmAt_lt_V {Z s : Ordinal.{0}} (hs : s ∈ K.At Z) : s < K.V := by
  obtain ⟨c, hc, -, rfl⟩ := hs
  exact gcG_lt hc

/-- **A code over `Z ≤ Ω₁` is below `Γ_{Ω₁+1+B}`.** -/
theorem gsmCl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (K.At Z) c) : c < K.V := by
  have hSC := (gsmV_SC (K := K))
  induction hc with
  | small h => exact (h.trans_le hZ).trans (gcG_Om1_lt _)
  | om => exact gcG_Om1_lt _
  | atom hs => exact gsmAt_lt_V hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

variable {S : InaccSeq.{0}}

/-- **`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}`** for every `c ≤ B`. -/
theorem gsm_psi (K : GsCS) (S : InaccSeq.{0}) : ∀ c : Ordinal.{0}, c ≤ K.B → S.psi c (Om (1 + 1)) = gcG c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  refine le_antisymm (gaPsi_le S (gcG_SC c) (gcG_Om1_lt c) fun e he => ?_)
    (gcG_le_of (ga_psi_SC c) (ga_Om1_lt_psi c) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hc)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hc)]
    have hβW : β < K.B := hβ.trans_le hc
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hβ (K.mem S _ _ β hβW hβ ?_)
    exact (K.gt_lt β hβW).trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi c)

theorem gsmV_psi (K : GsCS) (S : InaccSeq.{0}) : S.psi K.B (Om (1 + 1)) = K.V := gsm_psi K S _ le_rfl

theorem gsmV_lt_Om2 (K : GsCS) (S : InaccSeq.{0}) : K.V < Om (1 + 1) := by
  rw [← gsmV_psi K S]; exact psi_lt (InR_Om_succ 1) _

theorem gsm_B_lt_V (K : GsCS) : K.B < K.V := K.B_V

/-- An atom lies in every hull `Cl(a, b)` with `B < a` and `Z ≤ b`. -/
theorem gsmAt_mem {Z a b s : Ordinal.{0}} (ha : K.B < a) (hZb : Z ≤ b) (hs : s ∈ K.At Z) : s ∈ S.CSet a b := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  rw [← gsm_psi K S c hc.le]
  exact CSet.psi_mem (hc.trans ha) (InR_Om_succ 1) (ga_Om2_mem _ _) (K.mem S _ _ c hc (hc.trans ha) (hg.trans_le hZb))

/-- **A code over `Z` lies in every hull `Cl(a, b)` with `B < a` and `Z ≤ b`.** -/
theorem gsmCl_mem_CSet {Z a b : Ordinal.{0}} (ha : K.B < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z (K.At Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gsmAt_mem ha hZb hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `Γ_{Ω₁+1+B}` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z ≤ Ω₁`,
every member of `Cl(a, Z)` below `Γ_{Ω₁+1+B}` is a code over `Z`. -/
theorem gsmCl_of_CSet {Z a : Ordinal.{0}} (hZ : 0 < Z) (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < K.V → GxCl Z (K.At Z) x := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv =>
    hkey _ (CSet.add_mem (CSet.of_lt hu) (CSet.of_lt hv))
      (ph_SC_Om1.isPrincipal (hu.trans_le hZ1) (hv.trans_le hZ1))
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv =>
    hkey _ (CSet.phi_mem (CSet.of_lt hu) (CSet.of_lt hv)) (ph_SC_Om1.2 _ (hu.trans_le hZ1) _ (hv.trans_le hZ1))
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  intro x hx
  have hx' := hx
  have hG2 := (gsmV_lt_Om2 K S).le
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
  | @coll π e hπ hπ1 he1 _ ihe =>
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
    · -- `x = ψ_{Ω₂}(e)` with `e < B`
      have heW : e.1 < K.B := by
        by_contra hge
        push Not at hge
        have h5 : K.V ≤ S.psi e.1 (Om (1 + 1)) := by
          rw [← gsmV_psi K S]
          rcases hge.lt_or_eq with h4 | h4
          · exact (psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) h4 (K.B_mem S _ _ h4
            (K.κ_lt.trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi e.1)))).le
          · rw [h4]
        exact absurd (h.trans_le h5) (lt_irrefl _)
      rw [gsm_psi K S e.1 heW.le]
      have hec : GxCl Z (K.At Z) e.1 := ihe he1 (heW.trans (gsm_B_lt_V K))
      have hg := K.code_gate Z hZ1' hZ hZa hZp e.1 hec heW
      exact GxCl.atom (gsmG_atom heW hg)
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem gsm_support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (K.At Z) x) :
    ∃ Z' < Z, GxCl Z' (K.At Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact ⟨K.gt c + 1, hZ.isPrincipal hg h1, GxCl.atom (gsmG_atom hc (lt_add_one _))⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (gsmCl_mono (le_max_left _ _) g1) (gsmCl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (gsmCl_mono (le_max_left _ _) g1) (gsmCl_mono (le_max_right _ _) g2)⟩

theorem gsm_B_lt_A (K : GsCS) (η : Ordinal.{0}) : K.B < ConjT.Aη S η := by
  have h1 : K.B < K.V := gsm_B_lt_V K
  have h2 : K.V < Om (1 + 1) := gsmV_lt_Om2 K S
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  have h3 : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 h2ω
  exact h1.trans (h2.trans (h3.trans_le le_self_add))

theorem gsm_B_lt_A1 (K : GsCS) (η : Ordinal.{0}) : K.B < ConjT.Aη S η + 1 :=
  (gsm_B_lt_A (S := S) K η).trans_le le_self_add

/-- **Terms for the codes below `E`** (atoms of `K` over the base). -/
def GsmPoly (K : GsCS) (X : Xt.XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (K.At Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (K.At y) c

end Googology.Trans.PoR.InaccPsi.R2.Gs
