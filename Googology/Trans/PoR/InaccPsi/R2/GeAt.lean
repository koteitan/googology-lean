import Googology.Trans.PoR.InaccPsi.R2.GeDig

/-!
# Atoms over a base for every code below `Ω₁^ω`: `Γ_{Ω₁+1+c}` with `c < Ω₁^ω`, digits below `Z`; codes up to
`Γ_{Ω₁+Ω₁^ω}`

`R2.GdAt` with the atoms `Γ_{Ω₁+1+a}` (`a < Z`) and `Γ_{Ω₁·2}`; here every code `c < Ω₁^ω` of `R2.GeSub` whose digits
are below the base gives an atom: `geAt Z = {Γ_{Ω₁+1+c} : c < Ω₁^ω, gate c < Z}` (it contains `gdAt Z`).

* `geAt`, `geAt_GxAt`, `geAt_mono`, `geV = Γ_{Ω₁+Ω₁^ω}` (the bound), `geCl_lt_V`;
* `geW_mem` (**a code `c < Ω₁^ω` lies in every hull containing its digits**), `ge_psi` (**`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for
  every `c ≤ Ω₁^ω`**), `geV_psi`, `geV_lt_Om2`;
* `geCl_mem_CSet` (**a code over `Z` lies in every hull `Cl(a, b)` with `Ω₁^ω < a`, `Z ≤ b`**), `geCl_of_CSet` (**the
  hull below `geV` consists of codes** when every countable member of `Cl(a, Z)` is below `Z ≤ Ω₁`: a collapse
  `ψ_{Ω₂}(e)` below `geV` has `e < Ω₁^ω`, `e` a code, so its digits are below `Z`, `R2.GeDig.geCode_gate`), `geCl_mono`,
  `ge_support`;
* `GePoly X E` (**terms for the codes below `E`**, the atoms over the base).

No new axiom.  New definitions: `geAt`, `geV`, `GePoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The atoms over `Z`**: `Γ_{Ω₁+1+c}` for every code `c < Ω₁^ω` with digits below `Z`. -/
def geAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ c, c < geW ∧ gate c < Z ∧ s = gcG c}

/-- **The bound**: `Γ_{Ω₁+1+Ω₁^ω} = Γ_{Ω₁+Ω₁^ω}`. -/
noncomputable def geV : Ordinal.{0} := gcG geW

theorem geAt_GxAt (Z : Ordinal.{0}) : GxAt (geAt Z) := by
  rintro s ⟨c, -, -, rfl⟩
  exact ⟨gcG_SC c, gcG_Om1_lt c⟩

theorem geAt_mono {Z Z' : Ordinal.{0}} (h : Z ≤ Z') : geAt Z ⊆ geAt Z' := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc, hg.trans_le h, rfl⟩

theorem geCl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (geAt Z) c) : GxCl Z' (geAt Z') c :=
  hc.mono h (geAt_mono h)

theorem geG_atom {Z c : Ordinal.{0}} (hc : c < geW) (hg : gate c < Z) : gcG c ∈ geAt Z := ⟨c, hc, hg, rfl⟩

theorem gdAt_sub_geAt {Z : Ordinal.{0}} (hZ : 1 < Z) (hZ1 : Z ≤ Om1) : gdAt Z ⊆ geAt Z := by
  rintro s ⟨a, ha, rfl⟩
  rcases ha with ha | rfl
  · have haO : a < Om1 := ha.trans_le hZ1
    exact ⟨a, const_lt_W haO, by rw [(sb_const haO 0).2]; exact ha, rfl⟩
  · exact ⟨Om1, Om1_lt_W, by rw [(sb_Om1 0).2]; exact hZ, by rw [Br.Om1_eq]⟩

theorem geV_SC : SC geV := gcG_SC _

theorem geAt_lt_V {Z s : Ordinal.{0}} (hs : s ∈ geAt Z) : s < geV := by
  obtain ⟨c, hc, -, rfl⟩ := hs
  exact gcG_lt hc

theorem gcG_W_lt (c : Ordinal.{0}) : geW < gcG c := by
  have hS := gcG_SC c
  have hO : Om1 < gcG c := by rw [Br.Om1_eq]; exact gcG_Om1_lt c
  rw [geW_eq]
  have hE : ω ^ gcG c = gcG c := Low.opow_eq_self_of_SC hS
  have h1 : Om1 * ω < gcG c :=
    (InE.mul_lt hE hO (omega0_lt_inE hE))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h1
  rwa [hE] at this

theorem geAt_W_lt {Z s : Ordinal.{0}} (hs : s ∈ geAt Z) : geW < s := by
  obtain ⟨c, -, -, rfl⟩ := hs
  exact gcG_W_lt c

/-- **A code over `Z ≤ Ω₁` is below `geV`.** -/
theorem geCl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (geAt Z) c) : c < geV := by
  have hSC := geV_SC
  induction hc with
  | small h => exact (h.trans_le hZ).trans (gcG_Om1_lt _)
  | om => exact gcG_Om1_lt _
  | atom hs => exact geAt_lt_V hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

variable {S : InaccSeq.{0}}

/-- **A code `c < Ω₁^ω` lies in every hull that contains its digits.** -/
theorem geW_mem {a b : Ordinal.{0}} : ∀ (n : ℕ) (c : Ordinal.{0}), c < oP n → gtN n c < b → c ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  have hOn : ∀ n : ℕ, Om1 * (n : Ordinal.{0}) ∈ S.CSet a b := by
    intro n
    induction n with
    | zero => simpa using CSet.zero_mem (S := S) a b
    | succ n ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hO
  have hmul : ∀ (n : ℕ) (q : Ordinal.{0}), q < b → oP n * q ∈ S.CSet a b := by
    intro n q
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
    have hP : ω ^ (Om1 * (n : Ordinal.{0}) + g) ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.add_mem (hOn n) (CSet.of_lt hgb))
      rwa [veblen_zero_apply] at this
    have hPj : ∀ i : ℕ, ω ^ (Om1 * (n : Ordinal.{0}) + g) * (i : Ordinal.{0}) ∈ S.CSet a b := by
      intro i
      induction i with
      | zero => simpa using CSet.zero_mem (S := S) a b
      | succ i ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hP
    have e : oP n * q = ω ^ (Om1 * (n : Ordinal.{0}) + g) * (j : Ordinal.{0}) + oP n * q' := by
      conv_lhs => rw [← hdm, hj, mul_add, ← mul_assoc]
      rw [oP_eq, ← opow_add]
    rw [e]
    exact CSet.add_mem (hPj j) (IH q' (hq'lt.trans_le hgle) ((hq'lt.trans_le hgle).trans hq))
  intro n
  induction n with
  | zero =>
    intro c hc _
    rw [oP_zero, Order.lt_one_iff] at hc
    rw [hc]; exact CSet.zero_mem _ _
  | succ n ih =>
    intro c _ hg
    simp only [gtN, max_lt_iff] at hg
    rw [← Ordinal.div_add_mod c (oP n)]
    exact CSet.add_mem (hmul n _ hg.1) (ih _ (Ordinal.mod_lt c (oP_ne n)) hg.2)

theorem geW_mem' {a b c : Ordinal.{0}} (hc : c < geW) (hg : gate c < b) : c ∈ S.CSet a b := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 hc
  rw [(sbc_eq hn 0).2] at hg
  exact geW_mem n c hn hg

/-- `Ω₁^ω = ω^{ω^{Ω₁+1}}` lies in every hull. -/
theorem geW_inC {a b : Ordinal.{0}} : geW ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  have e : geW = veblen 0 (veblen 0 (Om1 + 1)) := by
    rw [veblen_zero_apply, veblen_zero_apply, geW_eq, opow_add, opow_one,
      show ω ^ Om1 = Om1 from Rj.rj_Om1_inE]
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.phi_mem (CSet.zero_mem _ _) (CSet.succ_mem hO))

/-- **`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}`** for every `c ≤ Ω₁^ω`. -/
theorem ge_psi (S : InaccSeq.{0}) : ∀ c : Ordinal.{0}, c ≤ geW → S.psi c (Om (1 + 1)) = gcG c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  refine le_antisymm (gaPsi_le S (gcG_SC c) (gcG_Om1_lt c) fun e he => ?_)
    (gcG_le_of (ga_psi_SC c) (ga_Om1_lt_psi c) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hc)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hc)]
    have hβW : β < geW := hβ.trans_le hc
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hβ (geW_mem' hβW ?_)
    exact (gate_lt_Om1 hβW).trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi c)

theorem geV_psi (S : InaccSeq.{0}) : S.psi geW (Om (1 + 1)) = geV := ge_psi S _ le_rfl

theorem geV_lt_Om2 (S : InaccSeq.{0}) : geV < Om (1 + 1) := by
  rw [← geV_psi S]; exact psi_lt (InR_Om_succ 1) _

/-- An atom lies in every hull `Cl(a, b)` with `Ω₁^ω < a` and `Z ≤ b`. -/
theorem geAt_mem {Z a b s : Ordinal.{0}} (ha : geW < a) (hZb : Z ≤ b) (hs : s ∈ geAt Z) : s ∈ S.CSet a b := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  rw [← ge_psi S c hc.le]
  exact CSet.psi_mem (hc.trans ha) (InR_Om_succ 1) (ga_Om2_mem _ _) (geW_mem' hc (hg.trans_le hZb))

/-- **A code over `Z` lies in every hull `Cl(a, b)` with `Ω₁^ω < a` and `Z ≤ b`.** -/
theorem geCl_mem_CSet {Z a b : Ordinal.{0}} (ha : geW < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z (geAt Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact geAt_mem ha hZb hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `geV` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z ≤ Ω₁`, every
member of `Cl(a, Z)` below `geV` is a code over `Z`. -/
theorem geCl_of_CSet {Z a : Ordinal.{0}} (hZ : 0 < Z) (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < geV → GxCl Z (geAt Z) x := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv =>
    hkey _ (CSet.add_mem (CSet.of_lt hu) (CSet.of_lt hv))
      (ph_SC_Om1.isPrincipal (hu.trans_le hZ1) (hv.trans_le hZ1))
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv =>
    hkey _ (CSet.phi_mem (CSet.of_lt hu) (CSet.of_lt hv)) (ph_SC_Om1.2 _ (hu.trans_le hZ1) _ (hv.trans_le hZ1))
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  intro x hx
  have hx' := hx
  have hG2 := (geV_lt_Om2 S).le
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
      have heW : e.1 < geW := by
        by_contra hge
        push Not at hge
        have h5 : geV ≤ S.psi e.1 (Om (1 + 1)) := by
          rw [← geV_psi S]
          rcases hge.lt_or_eq with h4 | h4
          · exact (psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) h4 geW_inC).le
          · rw [h4]
        exact absurd (h.trans_le h5) (lt_irrefl _)
      rw [ge_psi S e.1 heW.le]
      have hec : GxCl Z (geAt Z) e.1 := ihe he1 (heW.trans (gcG_W_lt 0 |>.trans_le (gcG_le zero_le)))
      have hg := geCode_gate hZ1' hZ hZa hZp (fun s hs => geAt_W_lt hs) hec heW
      exact GxCl.atom (geG_atom heW hg)
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem ge_support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (geAt Z) x) :
    ∃ Z' < Z, GxCl Z' (geAt Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact ⟨gate c + 1, hZ.isPrincipal hg h1, GxCl.atom (geG_atom hc (lt_add_one _))⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (geCl_mono (le_max_left _ _) g1) (geCl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (geCl_mono (le_max_left _ _) g1) (geCl_mono (le_max_right _ _) g2)⟩

theorem ge_W_lt_A (η : Ordinal.{0}) : geW < ConjT.Aη S η := by
  have h1 : geW < geV := gcG_W_lt geW
  have h2 : geV < Om (1 + 1) := geV_lt_Om2 S
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  have h3 : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 h2ω
  exact h1.trans (h2.trans (h3.trans_le le_self_add))

theorem ge_W_lt_A1 (η : Ordinal.{0}) : geW < ConjT.Aη S η + 1 := (ge_W_lt_A η).trans_le le_self_add

/-- **Terms for the codes below `E`** (atoms over the base): for every code `c < E` over `Z` some term of `X` has the
value `Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GePoly (X : Xt.XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (geAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (geAt y) c

end Googology.Trans.PoR.InaccPsi.R2.Ge
