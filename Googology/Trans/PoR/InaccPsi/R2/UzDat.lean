import Googology.Trans.PoR.InaccPsi.R2.UwFV

/-!
# The datum at `W` of every member of the visibility closure one threshold down, with no normal form

`W = Ω_{s+1}`, `L = Ω_s` (`s` finite), `K_v = Ul.UlK S s v`; `i < s`, `X = Ul.UlK S i q` (`q` strongly critical,
`q ≤ Ω_{i+1}`).  A *datum* of `y` is a `z ∈ X`, `z < W`, with `y ∈ K_v ↔ z < v` for every strongly critical `v`,
`L < v ≤ W` (`UzDat`).

* `uz_dat_small`, `uz_dat_all`, `uz_dat_one`, `uz_dat_two` (the four ways a datum is formed: a member below `W` is its
  own datum; `0` is a datum of a member of every `K_v`; a datum of `a` or the larger of the data of `a` and `b` is a
  datum of `x` when `x ∈ K_v` is determined by `a`, resp. by `a` and `b`);
* `uz_dat_of_comps` (**a datum of every principal summand gives a datum**);
* `uz_dat_comp` (**every principal summand of a member of the normalized closure `Uo.UoK S i q` has a datum**: by
  induction on the normalized derivation, summand by summand as in `Uo.uoG`; a collapse `ψ_π(e) ≥ W` is determined by
  its own argument `e` and its subscript `π`, `Uo.uoArg`, `Uo.uoSub`, whatever the size of `e`);
* `uz_dat` (**every `y ∈ X` has a datum**; no normal form, no hypothesis `y ∈ ⋃ a, Cl(a, 0)`).

No new axiom.  New definition: the statement name `UzDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Us

/-- **A datum of `y` at `W = Ω_{s+1}` inside `K^{(i)}_q`**: some `z ∈ K^{(i)}_q`, `z < W`, with `y ∈ K^{(s)}_v ↔ z < v`
for every strongly critical `v`, `Ω_s < v ≤ W`. -/
def UzDat (S : InaccSeq.{0}) (s i q y : Ordinal.{0}) : Prop :=
  ∃ z, UlK S i q z ∧ z < Om (s + 1) ∧
    ∀ v, SC v → Om s < v → v ≤ Om (s + 1) → (UlK S s v y ↔ z < v)

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- A member of `K^{(i)}_q` below `W` is its own datum. -/
theorem uz_dat_small (hs : s < ω) {i q y : Ordinal.{0}} (hyK : UlK S i q y) (hyW : y < Om (s + 1)) :
    UzDat S s i q y :=
  ⟨y, hyK, hyW, fun _ hv hLv _ => ⟨fun h => ulK_lt_W hs hv hLv h hyW, UlK.small⟩⟩

/-- `0` is a datum of a member of every `K^{(s)}_v`. -/
theorem uz_dat_all {i q y : Ordinal.{0}} (hy : ∀ v, SC v → Om s < v → v ≤ Om (s + 1) → UlK S s v y) :
    UzDat S s i q y :=
  ⟨0, UlK.zero, (Ui.ui_SC_W s).1, fun v hv hLv hvW => ⟨fun _ => hv.1, fun _ => hy v hv hLv hvW⟩⟩

/-- A datum of `a` is a datum of `x` when `x ∈ K^{(s)}_v` is determined by `a`. -/
theorem uz_dat_one {i q x a : Ordinal.{0}} (ha : UzDat S s i q a)
    (h : ∀ v, SC v → Om s < v → v ≤ Om (s + 1) → (UlK S s v x ↔ UlK S s v a)) : UzDat S s i q x := by
  obtain ⟨z, hzK, hzW, hz⟩ := ha
  exact ⟨z, hzK, hzW, fun v hv hLv hvW => (h v hv hLv hvW).trans (hz v hv hLv hvW)⟩

/-- The larger of the data of `a` and `b` is a datum of `x` when `x ∈ K^{(s)}_v` is determined by `a` and `b`. -/
theorem uz_dat_two {i q x a b : Ordinal.{0}} (ha : UzDat S s i q a) (hb : UzDat S s i q b)
    (h : ∀ v, SC v → Om s < v → v ≤ Om (s + 1) → (UlK S s v x ↔ UlK S s v a ∧ UlK S s v b)) :
    UzDat S s i q x := by
  obtain ⟨za, hzaK, hzaW, hza⟩ := ha
  obtain ⟨zb, hzbK, hzbW, hzb⟩ := hb
  refine ⟨max za zb, ?_, max_lt hzaW hzbW, fun v hv hLv hvW => ?_⟩
  · rcases le_total za zb with h' | h'
    · rw [max_eq_right h']; exact hzbK
    · rw [max_eq_left h']; exact hzaK
  · rw [h v hv hLv hvW, hza v hv hLv hvW, hzb v hv hLv hvW, max_lt_iff]

/-- **A datum of every principal summand gives a datum.** -/
theorem uz_dat_of_comps {i q : Ordinal.{0}} :
    ∀ x : Ordinal.{0}, (∀ g, Comp g x → UzDat S s i q (ω ^ g)) → UzDat S s i q x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hc
  rcases eq_or_ne x 0 with rfl | hx0
  · exact uz_dat_all fun _ _ _ _ => UlK.zero
  have hl : UzDat S s i q (lead x) := hc _ (comp_lead hx0)
  have ht : UzDat S s i q (tail x) := IH _ (tail_lt hx0) fun g hg => hc g (Comp.of_tail hx0 hg)
  refine uz_dat_two hl ht fun v hv _ _ => ⟨fun h => uoK_lead_tail hv h hx0, fun h => ?_⟩
  have := UlK.add h.1 h.2; rwa [lead_add_tail hx0] at this

/-- **Every principal summand of a member of the normalized closure `UoK S i q` has a datum at `W`** (`i < s`, `q`
strongly critical, `q ≤ Ω_{i+1}`). -/
theorem uz_dat_comp (hs : s < ω) {i q : Ordinal.{0}} (his : i < s) (hqL : q ≤ Om (i + 1)) :
    ∀ x, UoK S i q x → ∀ g, Comp g x → UzDat S s i q (ω ^ g) := by
  have hqs : q < Om (s + 1) :=
    hqL.trans_lt ((Om_le_Om.2 (Order.add_one_le_of_lt his)).trans_lt (Om_lt_Om.2 (lt_add_one s)))
  intro x hx
  induction hx with
  | @small y h =>
    intro g hg
    have hlt : ω ^ g < q := hg.opow_le.trans_lt h
    exact uz_dat_small hs (UlK.small hlt) (hlt.trans hqs)
  | zero => intro g hg; exact absurd hg (not_comp_zero g)
  | inacc n =>
    intro g hg
    rw [Comp.eq_of_principal (SC_I n).isPrincipal (S.I_ne_zero n) hg]
    exact uz_dat_all fun _ _ _ _ => UlK.inacc n
  | inaccW =>
    intro g hg
    rw [Comp.eq_of_principal SC_Iw.isPrincipal S.Iw_ne_zero hg]
    exact uz_dat_all fun _ _ _ _ => UlK.inaccW
  | add _ _ ihx ihy =>
    intro g hg
    rcases Comp.add hg with h | h
    · exact ihx g h
    · exact ihy g h
  | @phi a b _ _ iha ihb =>
    intro g hg
    rw [Comp.eq_of_principal (veblen_isPrincipal a b) veblen_pos.ne' hg]
    have hda := uz_dat_of_comps a iha
    have hdb := uz_dat_of_comps b ihb
    by_cases ea : veblen a b = a
    · rw [ea]; exact hda
    by_cases eb : veblen a b = b
    · rw [eb]; exact hdb
    have hal : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) (Ne.symm ea)
    have hbl : b < veblen a b := lt_of_le_of_ne (right_le_veblen a b) (Ne.symm eb)
    exact uz_dat_two hda hdb fun _ _ _ _ => ⟨fun h => uoK_veb h hal hbl, fun h => UlK.phi h.1 h.2⟩
  | @om a _ iha =>
    intro g hg
    have ha0 : a ≠ 0 := by rintro rfl; rw [Om_zero] at hg; exact not_comp_zero g hg
    rw [Comp.eq_of_principal (SC_Om ha0).isPrincipal (Om_pos ha0).ne' hg]
    exact uz_dat_one (uz_dat_of_comps a iha) fun _ _ _ _ => ⟨uoK_Om, UlK.om⟩
  | @coll π e hπ hπi hπU heU hown ihπ ihe =>
    intro g hg
    have hxSC := SC_psi hπ e
    rw [Comp.eq_of_principal hxSC.isPrincipal hxSC.1.ne' hg]
    by_cases hxW : S.psi e π < Om (s + 1)
    · exact uz_dat_small hs (UlK.coll hπ hπi hπU.toK heU.toK) hxW
    have hWx : Om (s + 1) ≤ S.psi e π := not_lt.1 hxW
    have hπW : π ≠ Om (s + 1) := by
      rintro rfl; exact hxW (psi_lt (InR_Om_succ s) e)
    refine uz_dat_two (uz_dat_of_comps e ihe) (uz_dat_of_comps π ihπ) fun v _ _ hvW => ⟨fun h => ?_, fun h =>
      UlK.coll hπ hπW h.2 h.1⟩
    have hvΛ : v ≤ S.Lam := us_qΛ hs hvW
    exact ⟨uoArg hvΛ hπ hown h (hvW.trans hWx), uoSub hvΛ hπ hown h (hvW.trans hWx)⟩

/-- **Every member of `K^{(i)}_q` has a datum at `W`** (`i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`): some
`z ∈ K^{(i)}_q`, `z < W`, with `y ∈ K^{(s)}_v ↔ z < v` for every strongly critical `v`, `Ω_s < v ≤ W`. -/
theorem uz_dat (hs : s < ω) {i q y : Ordinal.{0}} (his : i < s) (hqL : q ≤ Om (i + 1)) (hy : UlK S i q y) :
    ∃ z, UlK S i q z ∧ z < Om (s + 1) ∧
      ∀ v, SC v → Om s < v → v ≤ Om (s + 1) → (UlK S s v y ↔ z < v) :=
  uz_dat_of_comps y (uz_dat_comp hs his hqL y (uoK_of_K (us_qΛ (his.trans hs) hqL) hy))

end Googology.Trans.PoR.InaccPsi.R2.Uz
