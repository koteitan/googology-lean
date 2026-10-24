import Googology.Trans.PoR.InaccPsi.R2.GhTow

/-!
# Atoms over a base for every code below `ε_{Ω₁+1}·ω`: `Γ_{Ω₁+1+c}`, gate of `c mod ε_{Ω₁+1}` below `Z`; codes up to
`Γ_{Ω₁+1+ε_{Ω₁+1}·ω}`

`R2.GfAt` with the codes `c = ε_{Ω₁+1}·m + r` (`m < ω`, `r < ε_{Ω₁+1}`): `ghAt Z = {Γ_{Ω₁+1+c} : c < ε_{Ω₁+1}·ω,
gtc(c mod ε_{Ω₁+1}) < Z}` (it contains `Gf.gfAt Z`, and the atom `Γ_{Ω₁+1+ε_{Ω₁+1}}` with gate `0`), the bound
`ghV = Γ_{Ω₁+1+ε_{Ω₁+1}·ω}`.

* `ghE = ε_{Ω₁+1}·ω`, `ghg c = gtc (c mod ε_{Ω₁+1})`, `gh_mod_big` / `gh_mod_small` (the remainder of a sum),
  `gh_shift` (`(ε_{Ω₁+1}·(n+1) + a) mod ε_{Ω₁+1} = a`);
* `gh_code_gate` (**a code `c < ε_{Ω₁+1}·ω` over `Z` has `ghg c < Z`**: by induction on the code; the only
  additively principal value in `[ε_{Ω₁+1}, ε_{Ω₁+1}·ω)` is `ε_{Ω₁+1}`);
* `ghAt`, `ghAt_GxAt`, `ghAt_mono`, `ghCl_mono`, `ghV`, `gfAt_sub_ghAt`, `gh_mem` (**every code `c < ε_{Ω₁+1}·ω`
  lies in every hull containing the digits of its remainder**), `gh_psi` (**`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for every
  `c ≤ ε_{Ω₁+1}·ω`**), `ghV_psi`, `ghV_lt_Om2`, `ghCl_mem_CSet`, `ghCl_of_CSet` (**the hull below `ghV` consists of
  codes**), `gh_support`, `gh_W_lt_A`, `GhPoly`.

No new axiom.  New definitions: `ghE`, `ghg`, `ghAt`, `ghV`, `GhPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The codes below `ε_{Ω₁+1}·ω`: quotient and remainder -/

/-- **The bound of the codes**: `ε_{Ω₁+1}·ω`. -/
noncomputable def ghE : Ordinal.{0} := gfE * ω

/-- **The gate of a code**: the gate of its remainder mod `ε_{Ω₁+1}`. -/
noncomputable def ghg (c : Ordinal.{0}) : Ordinal.{0} := gtc (c % gfE)

theorem gfE_ne : gfE ≠ 0 := eW_E.pos.ne'

theorem ghg_of_lt {c : Ordinal.{0}} (hc : c < gfE) : ghg c = gtc c := by rw [ghg, Ordinal.mod_eq_of_lt hc]

theorem gh_mod_lt (c : Ordinal.{0}) : c % gfE < gfE := Ordinal.mod_lt c gfE_ne

theorem gfE_lt_ghE : gfE < ghE := lt_mul_of_one_lt_right eW_E.pos one_lt_omega0

theorem ghE_eq : ghE = ω ^ (gfE + 1) := by rw [ghE, opow_add, opow_one, show ω ^ gfE = gfE from eW_E]

theorem gh_div_nat {c : Ordinal.{0}} (hc : c < ghE) : ∃ m : ℕ, c / gfE = m :=
  lt_omega0.1 ((Ordinal.div_lt gfE_ne).2 hc)

/-- The remainder of a sum whose right summand is at least `ε_{Ω₁+1}`. -/
theorem gh_mod_big (u : Ordinal.{0}) {v : Ordinal.{0}} (hv : gfE ≤ v) : (u + v) % gfE = v % gfE := by
  have hq : 1 ≤ v / gfE := by
    rw [Order.one_le_iff_pos, Ordinal.div_pos gfE_ne]; exact hv
  have e1 : v / gfE = 1 + (v / gfE - 1) := (Ordinal.add_sub_cancel_of_le hq).symm
  have hab : u % gfE + gfE = gfE := Ordinal.add_absorp (b := gfE)
    (by rw [show ω ^ gfE = gfE from eW_E]; exact gh_mod_lt u) (by rw [show ω ^ gfE = gfE from eW_E])
  have e2 : u % gfE + gfE * (v / gfE) = gfE * (v / gfE) := by
    rw [e1, mul_add, mul_one, ← add_assoc, hab]
  have e : u + v = gfE * (u / gfE + v / gfE) + v % gfE := by
    conv_lhs => rw [← Ordinal.div_add_mod u gfE, ← Ordinal.div_add_mod v gfE]
    rw [add_assoc, ← add_assoc (u % gfE), e2, ← add_assoc, ← mul_add]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (gh_mod_lt v)]

/-- The remainder of a sum whose right summand is below `ε_{Ω₁+1}`. -/
theorem gh_mod_small (u : Ordinal.{0}) {v : Ordinal.{0}} (hv : v < gfE) : (u + v) % gfE = u % gfE + v := by
  have e : u + v = gfE * (u / gfE) + (u % gfE + v) := by
    conv_lhs => rw [← Ordinal.div_add_mod u gfE]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (eW_indec.add_lt (gh_mod_lt u) hv)]

theorem gh_shift (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) :
    (gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a) % gfE = a ∧ ghg (gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a) = gtc a := by
  have e : (gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a) % gfE = a := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt ha]
  exact ⟨e, by rw [ghg, e]⟩

theorem gh_shift_lt (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) : gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a < ghE := by
  rw [ghE]
  calc gfE * ((n + 1 : ℕ) : Ordinal.{0}) + a < gfE * ((n + 1 : ℕ) : Ordinal.{0}) + gfE :=
        (add_lt_add_iff_left _).2 ha
    _ = gfE * ((n + 1 + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ (n + 1), mul_add_one]
    _ < gfE * ω := (mul_lt_mul_iff_right₀ eW_E.pos).2 (natCast_lt_omega0 _)

/-- **Every additively principal ordinal in `[ε_{Ω₁+1}, ε_{Ω₁+1}·ω)` is `ε_{Ω₁+1}`.** -/
theorem gh_opow_eq {e : Ordinal.{0}} (h1 : gfE ≤ ω ^ e) (h2 : ω ^ e < ghE) : ω ^ e = gfE := by
  rw [ghE_eq] at h2
  have he1 : e < gfE + 1 := (opow_lt_opow_iff_right one_lt_omega0).1 h2
  have he2 : gfE ≤ e := by
    rw [← show ω ^ gfE = gfE from eW_E] at h1
    exact (opow_le_opow_iff_right one_lt_omega0).1 h1
  rw [le_antisymm (Order.lt_add_one_iff.1 he1) he2]; exact eW_E

/-- **The gate of a code below `ε_{Ω₁+1}·ω`**: a code over `Z` (atoms above `ε_{Ω₁+1}·ω`) has `ghg c < Z`. -/
theorem gh_code_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, ghE < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < ghE → ghg c < Z := by
  have hAt' : ∀ s ∈ At, gfE < s := fun s hs => gfE_lt_ghE.trans (hAt s hs)
  have hsmall : ∀ x, GxCl Z At x → x < gfE → ghg x < Z := fun x hx h => by
    rw [ghg_of_lt h]; exact gfCode_gate hZ1 hZ0 hZa hZp hAt' hx h
  have hZ0' : gtc 0 < Z := by rw [gtc_zero]; exact hZ0
  have hgfE : ghg gfE = gtc 0 := by rw [ghg, Ordinal.mod_self]
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans Om1_lt_eW)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact Om1_lt_eW)
  | @atom s hs => exact fun h => absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (x + y) gfE with hlt | hge
    · exact hsmall _ (GxCl.add hx hy) hlt
    have hxE : x < ghE := lt_of_le_of_lt le_self_add h
    have hyE : y < ghE := lt_of_le_of_lt le_add_self h
    rcases le_or_gt gfE y with hy' | hy'
    · rw [ghg, gh_mod_big x hy']; exact ihy hyE
    · have hx' : gfE ≤ x := by
        by_contra hx'
        push Not at hx'
        exact absurd (eW_indec.add_lt hx' hy') (not_lt.2 hge)
      have hyg : gtc y < Z := by rw [← ghg_of_lt hy']; exact hsmall _ hy hy'
      rw [ghg, gh_mod_small x hy']
      exact gtc_add hZa _ _ (gh_mod_lt x) hy' (ihx hxE) hyg
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) gfE with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    have hp : ∃ e : Ordinal.{0}, veblen x y = ω ^ e := by
      rcases eq_or_ne x 0 with rfl | hx0
      · exact ⟨y, veblen_zero_apply y⟩
      · refine ⟨veblen x y, ?_⟩
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rw [veblen_zero_apply] at this
        exact this.symm
    obtain ⟨e, he⟩ := hp
    rw [he] at hge h ⊢
    rw [gh_opow_eq hge h, hgfE]
    exact hZ0'

/-! ## The atoms -/

/-- **The atoms over `Z`**: `Γ_{Ω₁+1+c}` for every code `c < ε_{Ω₁+1}·ω` with `ghg c < Z`. -/
def ghAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | ∃ c, c < ghE ∧ ghg c < Z ∧ s = gcG c}

/-- **The bound**: `Γ_{Ω₁+1+ε_{Ω₁+1}·ω}`. -/
noncomputable def ghV : Ordinal.{0} := gcG ghE

theorem ghAt_GxAt (Z : Ordinal.{0}) : GxAt (ghAt Z) := by
  rintro s ⟨c, -, -, rfl⟩
  exact ⟨gcG_SC c, gcG_Om1_lt c⟩

theorem ghAt_mono {Z Z' : Ordinal.{0}} (h : Z ≤ Z') : ghAt Z ⊆ ghAt Z' := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc, hg.trans_le h, rfl⟩

theorem ghCl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (ghAt Z) c) : GxCl Z' (ghAt Z') c :=
  hc.mono h (ghAt_mono h)

theorem ghG_atom {Z c : Ordinal.{0}} (hc : c < ghE) (hg : ghg c < Z) : gcG c ∈ ghAt Z := ⟨c, hc, hg, rfl⟩

theorem gfAt_sub_ghAt (Z : Ordinal.{0}) : gfAt Z ⊆ ghAt Z := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc.trans gfE_lt_ghE, by rw [ghg_of_lt hc]; exact hg, rfl⟩

theorem gfCl_ghCl {Z c : Ordinal.{0}} (hc : GxCl Z (gfAt Z) c) : GxCl Z (ghAt Z) c :=
  hc.mono le_rfl (gfAt_sub_ghAt Z)

theorem ghV_SC : SC ghV := gcG_SC _

theorem ghAt_lt_V {Z s : Ordinal.{0}} (hs : s ∈ ghAt Z) : s < ghV := by
  obtain ⟨c, hc, -, rfl⟩ := hs
  exact gcG_lt hc

theorem gcG_ghE_lt (c : Ordinal.{0}) : ghE < gcG c := by
  have hE : InE (gcG c) := Low.opow_eq_self_of_SC (gcG_SC c)
  exact hE.mul_lt (gcG_eW_lt c) (omega0_lt_inE hE)

theorem ghAt_W_lt {Z s : Ordinal.{0}} (hs : s ∈ ghAt Z) : ghE < s := by
  obtain ⟨c, -, -, rfl⟩ := hs
  exact gcG_ghE_lt c

/-- **A code over `Z ≤ Ω₁` is below `ghV`.** -/
theorem ghCl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (ghAt Z) c) : c < ghV := by
  have hSC := ghV_SC
  induction hc with
  | small h => exact (h.trans_le hZ).trans (gcG_Om1_lt _)
  | om => exact gcG_Om1_lt _
  | atom hs => exact ghAt_lt_V hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

variable {S : InaccSeq.{0}}

/-- **Every code `c < ε_{Ω₁+1}·ω` lies in every hull containing the digits of its remainder**
(`c = ε_{Ω₁+1}·m + r`, `ε_{Ω₁+1} = φ(1, Ω₁+1)`). -/
theorem gh_mem {a b c : Ordinal.{0}} (hc : c < ghE) (hg : ghg c < b) : c ∈ S.CSet a b := by
  obtain ⟨m, hm⟩ := gh_div_nat hc
  have e : c = gfE * (m : Ordinal.{0}) + c % gfE := by
    conv_lhs => rw [← Ordinal.div_add_mod c gfE]
    rw [hm]
  have h1 : gfE * (m : Ordinal.{0}) ∈ S.CSet a b := lg_cset_mul_nat gfW_inC m
  rw [e]
  exact CSet.add_mem h1 (gfW_mem' (gh_mod_lt c) hg)

theorem ghg_lt_Om1 (c : Ordinal.{0}) : ghg c < Om1 := gtc_lt_Om1 _ (gh_mod_lt c)

/-- **`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}`** for every `c ≤ ε_{Ω₁+1}·ω`. -/
theorem gh_psi (S : InaccSeq.{0}) : ∀ c : Ordinal.{0}, c ≤ ghE → S.psi c (Om (1 + 1)) = gcG c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  refine le_antisymm (gaPsi_le S (gcG_SC c) (gcG_Om1_lt c) fun e he => ?_)
    (gcG_le_of (ga_psi_SC c) (ga_Om1_lt_psi c) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hc)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hc)]
    have hβW : β < ghE := hβ.trans_le hc
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hβ (gh_mem hβW ?_)
    exact (ghg_lt_Om1 β).trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi c)

theorem ghV_psi (S : InaccSeq.{0}) : S.psi ghE (Om (1 + 1)) = ghV := gh_psi S _ le_rfl

theorem ghV_lt_Om2 (S : InaccSeq.{0}) : ghV < Om (1 + 1) := by
  rw [← ghV_psi S]; exact psi_lt (InR_Om_succ 1) _

/-- `ε_{Ω₁+1}·ω` lies in every hull. -/
theorem ghE_inC {a b : Ordinal.{0}} : ghE ∈ S.CSet a b := by
  rw [ghE_eq]
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.add_mem (gfW_inC (S := S) (a := a) (b := b))
    (CSet.one_mem _ _))
  rwa [veblen_zero_apply] at this

/-- An atom lies in every hull `Cl(a, b)` with `ε_{Ω₁+1}·ω < a` and `Z ≤ b`. -/
theorem ghAt_mem {Z a b s : Ordinal.{0}} (ha : ghE < a) (hZb : Z ≤ b) (hs : s ∈ ghAt Z) : s ∈ S.CSet a b := by
  obtain ⟨c, hc, hg, rfl⟩ := hs
  rw [← gh_psi S c hc.le]
  exact CSet.psi_mem (hc.trans ha) (InR_Om_succ 1) (ga_Om2_mem _ _) (gh_mem hc (hg.trans_le hZb))

/-- **A code over `Z` lies in every hull `Cl(a, b)` with `ε_{Ω₁+1}·ω < a` and `Z ≤ b`.** -/
theorem ghCl_mem_CSet {Z a b : Ordinal.{0}} (ha : ghE < a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z (ghAt Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact ghAt_mem ha hZb hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `ghV` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z ≤ Ω₁`, every
member of `Cl(a, Z)` below `ghV` is a code over `Z`. -/
theorem ghCl_of_CSet {Z a : Ordinal.{0}} (hZ : 0 < Z) (hZ1 : Z ≤ Om 1)
    (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < ghV → GxCl Z (ghAt Z) x := by
  have hZa : ∀ u v, u < Z → v < Z → u + v < Z := fun u v hu hv =>
    hkey _ (CSet.add_mem (CSet.of_lt hu) (CSet.of_lt hv))
      (ph_SC_Om1.isPrincipal (hu.trans_le hZ1) (hv.trans_le hZ1))
  have hZp : ∀ u v, u < Z → v < Z → veblen u v < Z := fun u v hu hv =>
    hkey _ (CSet.phi_mem (CSet.of_lt hu) (CSet.of_lt hv)) (ph_SC_Om1.2 _ (hu.trans_le hZ1) _ (hv.trans_le hZ1))
  have hZ1' : Z ≤ Om1 := by rw [Br.Om1_eq]; exact hZ1
  intro x hx
  have hx' := hx
  have hG2 := (ghV_lt_Om2 S).le
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
    · -- `x = ψ_{Ω₂}(e)` with `e < ε_{Ω₁+1}·ω`
      have heW : e.1 < ghE := by
        by_contra hge
        push Not at hge
        have h5 : ghV ≤ S.psi e.1 (Om (1 + 1)) := by
          rw [← ghV_psi S]
          rcases hge.lt_or_eq with h4 | h4
          · exact (psi_lt_psi_of_mem (S := S) (InR_Om_succ 1) h4 ghE_inC).le
          · rw [h4]
        exact absurd (h.trans_le h5) (lt_irrefl _)
      rw [gh_psi S e.1 heW.le]
      have hec : GxCl Z (ghAt Z) e.1 := ihe he1 (heW.trans (gcG_ghE_lt 0 |>.trans_le (gcG_le zero_le)))
      have hg := gh_code_gate hZ1' hZ hZa hZp (fun s hs => ghAt_W_lt hs) hec heW
      exact GxCl.atom (ghG_atom heW hg)
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans (h.trans_le hG2)) (lt_irrefl _)

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem gh_support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (ghAt Z) x) :
    ∃ Z' < Z, GxCl Z' (ghAt Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact ⟨ghg c + 1, hZ.isPrincipal hg h1, GxCl.atom (ghG_atom hc (lt_add_one _))⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (ghCl_mono (le_max_left _ _) g1) (ghCl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (ghCl_mono (le_max_left _ _) g1) (ghCl_mono (le_max_right _ _) g2)⟩

theorem gh_W_lt_A (η : Ordinal.{0}) : ghE < ConjT.Aη S η := by
  have h1 : ghE < ghV := gcG_ghE_lt ghE
  have h2 : ghV < Om (1 + 1) := ghV_lt_Om2 S
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  have h3 : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 h2ω
  exact h1.trans (h2.trans (h3.trans_le le_self_add))

theorem gh_W_lt_A1 (η : Ordinal.{0}) : ghE < ConjT.Aη S η + 1 := (gh_W_lt_A η).trans_le le_self_add

/-- **Terms for the codes below `E`** (atoms over the base): for every code `c < E` over `Z` some term of `X` has the
value `Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GhPoly (X : Xt.XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (ghAt Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y (ghAt y) c

end Googology.Trans.PoR.InaccPsi.R2.Gh
