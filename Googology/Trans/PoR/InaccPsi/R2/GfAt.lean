import Googology.Trans.PoR.InaccPsi.R2.GfDig

/-!
# Atoms over a base for every code below `ε_{Ω₁+1}`: `Γ_{Ω₁+1+c}` with `c < ε_{Ω₁+1}`, gate below `Z`; codes up to
`Γ_{Ω₁+ε_{Ω₁+1}}`

`R2.GeAt` with the hereditary codes of `R2.GfSub`: `gfAt Z = {Γ_{Ω₁+1+c} : c < ε_{Ω₁+1}, gtc c < Z}` (it contains
`gdAt Z`), the bound `gfV = Γ_{Ω₁+1+ε_{Ω₁+1}}`.

* `gfAt`, `gfAt_GxAt`, `gfAt_mono`, `gfV`, `gcG_eW_lt` (`ε_{Ω₁+1} < Γ_{Ω₁+1+c}`), `gfCl_lt_V`;
* `gfW_mem` (**a code `c < ε_{Ω₁+1}` and `Ω₁·c` lie in every hull containing its digits**, one induction on the code),
  `gfW_inC` (`ε_{Ω₁+1} = φ(1, Ω₁+1)` lies in every hull), `gf_psi` (**`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for every
  `c ≤ ε_{Ω₁+1}`**), `gfV_psi`, `gfV_lt_Om2`;
* `gfCl_mem_CSet`, `gfCl_of_CSet` (**the hull below `gfV` consists of codes** when every countable member of
  `Cl(a, Z)` is below `Z ≤ Ω₁`: a collapse `ψ_{Ω₂}(e)` below `gfV` has `e < ε_{Ω₁+1}`, `e` a code over `Z`, so its gate
  is below `Z`, `R2.GfDig.gfCode_gate`), `gfCl_mono`, `gf_support`;
* `GfPoly X E` (**terms for the codes below `E`**, the atoms over the base).

No new axiom.  New definitions: `gfAt`, `gfV`, `GfPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The atoms over `Z`**: `Γ_{Ω₁+1+c}` for every code `c < Ω₁^ω` with digits below `Z`. -/
def gfAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ c, c < gfE ∧ gtc c < Z ∧ s = gcG c}

/-- **The bound**: `Γ_{Ω₁+1+Ω₁^ω} = Γ_{Ω₁+Ω₁^ω}`. -/
noncomputable def gfV : Ordinal.{0} := gcG gfE

theorem gfAt_GxAt (Z : Ordinal.{0}) : GxAt (gfAt Z) := by
  rintro s ⟨c, -, -, rfl⟩
  exact ⟨gcG_SC c, gcG_Om1_lt c⟩

theorem gfAt_mono {Z Z' : Ordinal.{0}} (h : Z ≤ Z') : gfAt Z ⊆ gfAt Z' := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc, hg.trans_le h, rfl⟩

theorem gfCl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (gfAt Z) c) : GxCl Z' (gfAt Z') c :=
  hc.mono h (gfAt_mono h)

theorem gfG_atom {Z c : Ordinal.{0}} (hc : c < gfE) (hg : gtc c < Z) : gcG c ∈ gfAt Z := ⟨c, hc, hg, rfl⟩

theorem gdAt_sub_gfAt {Z : Ordinal.{0}} (hZ : 1 < Z) (hZ1 : Z ≤ Om1) : gdAt Z ⊆ gfAt Z := by
  rintro s ⟨a, ha, rfl⟩
  rcases ha with ha | rfl
  · have haO : a < Om1 := ha.trans_le hZ1
    exact ⟨a, const_lt_eW haO, by rw [(rdc_const haO 0).2]; exact ha, rfl⟩
  · exact ⟨Om1, Om1_lt_eW, by rw [(rdc_Om1 0).2]; exact hZ, by rw [Br.Om1_eq]⟩

theorem gfV_SC : SC gfV := gcG_SC _

theorem gfAt_lt_V {Z s : Ordinal.{0}} (hs : s ∈ gfAt Z) : s < gfV := by
  obtain ⟨c, hc, -, rfl⟩ := hs
  exact gcG_lt hc

theorem gcG_eW_lt (c : Ordinal.{0}) : gfE < gcG c := by
  have hS := gcG_SC c
  have hO : Om1 < gcG c := by rw [Br.Om1_eq]; exact gcG_Om1_lt c
  rw [eW_eq]
  have h1 : (1 : Ordinal.{0}) < gcG c := gf_one_lt_Om1.trans hO
  have h2 : Om1 + 1 < gcG c := (inE_indec (Low.opow_eq_self_of_SC hS)).add_lt hO h1
  exact hS.2 1 h1 _ h2

theorem gfAt_W_lt {Z s : Ordinal.{0}} (hs : s ∈ gfAt Z) : gfE < s := by
  obtain ⟨c, -, -, rfl⟩ := hs
  exact gcG_eW_lt c

/-- **A code over `Z ≤ Ω₁` is below `gfV`.** -/
theorem gfCl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (gfAt Z) c) : c < gfV := by
  have hSC := gfV_SC
  induction hc with
  | small h => exact (h.trans_le hZ).trans (gcG_Om1_lt _)
  | om => exact gcG_Om1_lt _
  | atom hs => exact gfAt_lt_V hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

variable {S : InaccSeq.{0}}

/-- `ω^E · q` lies in every hull containing `E` and `q < b`. -/
theorem gfMul_mem {a b E : Ordinal.{0}} (hE : E ∈ S.CSet a b) : ∀ q, q < b → ω ^ E * q ∈ S.CSet a b := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  set g := log ω q with hg
  set m := q / ω ^ g with hm
  set q' := q % ω ^ g with hq'
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * m + q' = q := Ordinal.div_add_mod q (ω ^ g)
  have hq'lt : q' < ω ^ g := Ordinal.mod_lt q hω0
  have hgle : ω ^ g ≤ q := opow_log_le_self ω hq0
  have hmω : m < ω := div_opow_log_lt q one_lt_omega0
  obtain ⟨j, hj⟩ := lt_omega0.1 hmω
  have hgb : g < b := lt_of_le_of_lt (log_le_self ω q) hq
  have hP : ω ^ (E + g) ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.add_mem hE (CSet.of_lt hgb))
    rwa [veblen_zero_apply] at this
  have hPj : ∀ i : ℕ, ω ^ (E + g) * (i : Ordinal.{0}) ∈ S.CSet a b := by
    intro i
    induction i with
    | zero => simpa using CSet.zero_mem (S := S) a b
    | succ i ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hP
  have e : ω ^ E * q = ω ^ (E + g) * (j : Ordinal.{0}) + ω ^ E * q' := by
    conv_lhs => rw [← hdm, hj, mul_add, ← mul_assoc]
    rw [← opow_add]
  rw [e]
  exact CSet.add_mem (hPj j) (IH q' (hq'lt.trans_le hgle) ((hq'lt.trans_le hgle).trans hq))

/-- **A code `c < ε_{Ω₁+1}` and `Ω₁·c` lie in every hull that contains its digits** (one induction on the code:
`Ω₁^l·q = ω^{Ω₁·l}·q`, `Ω₁·Ω₁^l·q = ω^{Ω₁ + Ω₁·l}·q`). -/
theorem gfW_mem {a b : Ordinal.{0}} : ∀ c, c < gfE → gtc c < b → c ∈ S.CSet a b ∧ Om1 * c ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcW hg
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [mul_zero]; exact ⟨CSet.zero_mem _ _, CSet.zero_mem _ _⟩
  obtain ⟨-, -, -, hdec, hrc, -⟩ := parts hc0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hc0 hcW
  have hlc := log_lt hc0 hcW
  set l := log Om1 c with hl
  set q := c / Om1 ^ l with hq
  set r := c % Om1 ^ l with hr
  obtain ⟨-, hlO⟩ := IH _ hlc (hlc.trans hcW) (gl.trans_lt hg)
  obtain ⟨hr1, hr2⟩ := IH _ hrc (hrc.trans hcW) (gr.trans_lt hg)
  have hqb := gq.trans_lt hg
  refine ⟨?_, ?_⟩
  · have e : c = ω ^ (Om1 * l) * q + r := by rw [← Om1_pow_eq, hdec]
    rw [e]
    exact CSet.add_mem (gfMul_mem hlO _ hqb) hr1
  · have e : Om1 * c = ω ^ (Om1 + Om1 * l) * q + Om1 * r := by
      rw [← mul_one_add, ← Om1_pow_eq, opow_one_add, mul_assoc, ← mul_add, hdec]
    rw [e]
    exact CSet.add_mem (gfMul_mem (CSet.add_mem hO hlO) _ hqb) hr2

theorem gfW_mem' {a b c : Ordinal.{0}} (hc : c < gfE) (hg : gtc c < b) : c ∈ S.CSet a b := (gfW_mem c hc hg).1

/-- `ε_{Ω₁+1} = φ(1, Ω₁+1)` lies in every hull. -/
theorem gfW_inC {a b : Ordinal.{0}} : gfE ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  rw [eW_eq]
  exact CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem hO)

/-- **`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}`** for every `c ≤ Ω₁^ω`. -/
theorem gf_psi (S : InaccSeq.{0}) : ∀ c : Ordinal.{0}, c ≤ gfE → S.psi c (Om (1 + 1)) = gcG c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  refine le_antisymm (gaPsi_le S (gcG_SC c) (gcG_Om1_lt c) fun e he => ?_)
    (gcG_le_of (ga_psi_SC c) (ga_Om1_lt_psi c) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hc)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hc)]
    have hβW : β < gfE := hβ.trans_le hc
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hβ (gfW_mem' hβW ?_)
    exact (gtc_lt_Om1 _ hβW).trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi c)

theorem gfV_psi (S : InaccSeq.{0}) : S.psi gfE (Om (1 + 1)) = gfV := gf_psi S _ le_rfl

theorem gfV_lt_Om2 (S : InaccSeq.{0}) : gfV < Om (1 + 1) := by
  rw [← gfV_psi S]; exact psi_lt (InR_Om_succ 1) _

/-- An atom lies in every hull `Cl(a, b)` with `Ω₁^ω < a` and `Z ≤ b`. -/
theorem gfAt_mem {Z a b s : Ordinal.{0}} (ha : gfE < a) (hZb : Z ≤ b) (hs : s ∈ gfAt Z) : s ∈ S.CSet a b := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  rw [← gf_psi S c hc.le]
  exact CSet.psi_mem (hc.trans ha) (InR_Om_succ 1) (ga_Om2_mem _ _) (gfW_mem' hc (hg.trans_le hZb))

/-- **A code over `Z` lies in every hull `Cl(a, b)` with `Ω₁^ω < a` and `Z ≤ b`.** -/
theorem gfCl_mem_CSet {Z a b : Ordinal.{0}} (ha : gfE < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z (gfAt Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gfAt_mem ha hZb hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `gfV` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z ≤ Ω₁`, every
member of `Cl(a, Z)` below `gfV` is a code over `Z`. -/
theorem gfCl_of_CSet {Z a : Ordinal.{0}} (hZ : 0 < Z) (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < gfV → GxCl Z (gfAt Z) x := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv =>
    hkey _ (CSet.add_mem (CSet.of_lt hu) (CSet.of_lt hv))
      (ph_SC_Om1.isPrincipal (hu.trans_le hZ1) (hv.trans_le hZ1))
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv =>
    hkey _ (CSet.phi_mem (CSet.of_lt hu) (CSet.of_lt hv)) (ph_SC_Om1.2 _ (hu.trans_le hZ1) _ (hv.trans_le hZ1))
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  intro x hx
  have hx' := hx
  have hG2 := (gfV_lt_Om2 S).le
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
    · -- `x = ψ_{Ω₂}(e)` with `e < Ω₁^ω`
      have heW : e.1 < gfE := by
        by_contra hge
        push Not at hge
        have h5 : gfV ≤ S.psi e.1 (Om (1 + 1)) := by
          rw [← gfV_psi S]
          rcases hge.lt_or_eq with h4 | h4
          · exact (psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) h4 gfW_inC).le
          · rw [h4]
        exact absurd (h.trans_le h5) (lt_irrefl _)
      rw [gf_psi S e.1 heW.le]
      have hec : GxCl Z (gfAt Z) e.1 := ihe he1 (heW.trans (gcG_eW_lt 0 |>.trans_le (gcG_le zero_le)))
      have hg := gfCode_gate hZ1' hZ hZa hZp (fun s hs => gfAt_W_lt hs) hec heW
      exact GxCl.atom (gfG_atom heW hg)
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem gf_support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (gfAt Z) x) :
    ∃ Z' < Z, GxCl Z' (gfAt Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact ⟨gtc c + 1, hZ.isPrincipal hg h1, GxCl.atom (gfG_atom hc (lt_add_one _))⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (gfCl_mono (le_max_left _ _) g1) (gfCl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (gfCl_mono (le_max_left _ _) g1) (gfCl_mono (le_max_right _ _) g2)⟩

theorem gf_W_lt_A (η : Ordinal.{0}) : gfE < ConjT.Aη S η := by
  have h1 : gfE < gfV := gcG_eW_lt gfE
  have h2 : gfV < Om (1 + 1) := gfV_lt_Om2 S
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  have h3 : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 h2ω
  exact h1.trans (h2.trans (h3.trans_le le_self_add))

theorem gf_W_lt_A1 (η : Ordinal.{0}) : gfE < ConjT.Aη S η + 1 := (gf_W_lt_A η).trans_le le_self_add

/-- **Terms for the codes below `E`** (atoms over the base): for every code `c < E` over `Z` some term of `X` has the
value `Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GfPoly (X : Xt.XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (gfAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (gfAt y) c

end Googology.Trans.PoR.InaccPsi.R2.Gf
