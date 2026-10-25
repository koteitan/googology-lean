import Googology.Trans.PoR.InaccPsi.R2.UoK
import Googology.Trans.PoR.InaccPsi.R2.UlConv

/-!
# Downward visibility `Ul.UlDV` is a theorem; FWD and the lifted `ψ`-link with no hypothesis

`W = Ω_{s+1}`, `V = Ω_{s+2}`, `L = Ω_s`, `ψ_π = S.psi · π`, `K_q = Ul.UlK S s q`, `Hˡ_γ = Ul.ulH S s γ`.  For an
argument `B` in its own closure at `V` (`B ∈ Cl(B, ψ_V(B))`) and a bound `L < q ≤ Λ`, every
member of `K_q` that lies in `Cl(B, ψ_V(B))` lies in `Cl(B, q)`.  The proof runs over the normalized derivations of
`R2.UoK` (`K_q = UoK`), component by component: a collapse `ψ_π(e)` (`π ≠ W`, `e` own) in `Cl(B, ψ_V(B))` at or
above `q` has `π = V` and `ψ_V(e) < ψ_V(B)`, hence `e < B`, or lies at or above `ψ_V(B)`, where
`InaccSeq.arg_mem_of_psi_mem` gives `e < B`, `e ∈ Cl(B, ψ_V(B))`.

* `uo_comp_mem` (the principal summands of a member of `Cl(a, b)` are members), `uo_lift` (a member of
  `Cl(B, ψ_V(B))` whose summands in `Cl(B, ψ_V(B))` are in `Cl(B, q)` is in `Cl(B, q)`);
* `uoG` (**`K_q ∩ Cl(B, ψ_V(B)) ⊆ Cl(B, q)`**, summand by summand, along the normalized derivation), `uo_vis_mem`;
* `uoDV`, `uoDV0` (**`Ul.UlDV S s` for every finite `s`**: for an own `B`, every level `j ∈ K_{ψ_W(B)}` with `j < ψ_V(B)`
  lies in `Cl(B, ψ_W(B))`);
* `uo_fwd` (**FWD at every level `γ < V`**), `uo_eq_all` (**the lifted link `ψ_W(B + W^γ·D) = Hˡ_γ(c + D)` at every
  level `γ < V`**), `uo_phi_fwd`, `uo_phi_eq` (the instance `s = 0`, every level `μ < Ω₂`) — all with no hypothesis
  beyond the shape conditions of `Ul.ul_fwd`, `Ul.ul_eq_all`, `Ul.ul_phi_fwd`, `Ul.ul_phi_eq`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- The principal summands of a member of `Cl(a, b)` are members. -/
theorem uo_comp_mem {a b : Ordinal.{0}} : ∀ x, x ∈ S.CSet a b → ∀ g, Comp g x → ω ^ g ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx g hc
  have hx0 : x ≠ 0 := by rintro rfl; exact not_comp_zero g hc
  have hlt := lead_tail_mem hx hx0
  rw [← lead_add_tail hx0] at hc
  rcases Comp.add hc with h | h
  · have h' : Comp g (ω ^ Ordinal.log ω x) := h
    rw [Comp.eq_of_opow h']; exact hlt.1
  · exact IH _ (tail_lt hx0) hlt.2 g h

/-- A member of `C` whose principal summands in `C` are in `Cl(a, q)` is in `Cl(a, q)`. -/
theorem uo_lift {a q x : Ordinal.{0}} {C : Set Ordinal.{0}} (hC : ∀ g, Comp g x → x ∈ C → ω ^ g ∈ C)
    (h : ∀ g, Comp g x → ω ^ g ∈ C → ω ^ g ∈ S.CSet a q) (hx : x ∈ C) : x ∈ S.CSet a q :=
  mem_of_comps (CSet.zero_mem a q) (fun _ _ => CSet.add_mem) x fun g hg => h g hg (hC g hg hx)

theorem uo_comp_self (g : Ordinal.{0}) : Comp g (ω ^ g) :=
  ⟨0, 0, opow_pos _ omega0_pos, by rw [zero_add, add_zero]⟩

/-- **`K_q ∩ Cl(B, ψ_V(B)) ⊆ Cl(B, q)`**, summand by summand along the normalized derivation, for `B` own at `V`
and `L < q`. -/
theorem uoG (hs : s < ω) {B q : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1))))
    (hLq : Om s < q) : ∀ x, UoK S s q x → ∀ g, Comp g x →
      ω ^ g ∈ S.CSet B (S.psi B (Om (s + 1 + 1))) → ω ^ g ∈ S.CSet B q := by
  set C := S.CSet B (S.psi B (Om (s + 1 + 1))) with hCdef
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hCc : ∀ x, ∀ g, Comp g x → x ∈ C → ω ^ g ∈ C := fun x g hg hx => uo_comp_mem x hx g hg
  have hlift : ∀ x, (∀ g, Comp g x → ω ^ g ∈ C → ω ^ g ∈ S.CSet B q) → x ∈ C → x ∈ S.CSet B q :=
    fun x h hx => uo_lift (fun g hg => hCc x g hg) h hx
  have hVL : S.psi B (Om (s + 1 + 1)) ≤ S.Lam :=
    ((psi_lt hκV B).trans (lt_Lam_of_mem zero_le (Ui.ui_W_mem (S := S)
      (Ui.ui_s1_lt_omega hs) 0 0))).le
  intro x hx
  induction hx with
  | @small y h =>
    intro g hg _
    exact CSet.of_lt (hg.opow_le.trans_lt h)
  | zero => intro g hg; exact absurd hg (not_comp_zero g)
  | inacc n =>
    intro g hg _
    rw [Comp.eq_of_principal (SC_I n).isPrincipal (S.I_ne_zero n) hg]; exact CSet.I_mem _ _ n
  | inaccW =>
    intro g hg _
    rw [Comp.eq_of_principal SC_Iw.isPrincipal S.Iw_ne_zero hg]; exact CSet.Iw_mem _ _
  | add _ _ ihx ihy =>
    intro g hg hgC
    rcases Comp.add hg with h | h
    · exact ihx g h hgC
    · exact ihy g h hgC
  | @phi a b _ _ iha ihb =>
    intro g hg hgC
    have hxe := Comp.eq_of_principal (veblen_isPrincipal a b) veblen_pos.ne' hg
    rw [hxe] at hgC ⊢
    by_cases ea : veblen a b = a
    · rw [ea] at hgC ⊢; exact hlift a iha hgC
    by_cases eb : veblen a b = b
    · rw [eb] at hgC ⊢; exact hlift b ihb hgC
    have hal : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) (Ne.symm ea)
    have hbl : b < veblen a b := lt_of_le_of_ne (right_le_veblen a b) (Ne.symm eb)
    have hab : a ∈ C ∧ b ∈ C := by
      by_cases hsm : veblen a b < S.psi B (Om (s + 1 + 1))
      · exact ⟨CSet.of_lt (hal.trans hsm), CSet.of_lt (hbl.trans hsm)⟩
      · exact mem_of_veblen_mem hgC hal hbl
    exact CSet.phi_mem (hlift a iha hab.1) (hlift b ihb hab.2)
  | @om a _ iha =>
    intro g hg hgC
    have ha0 : a ≠ 0 := by rintro rfl; rw [Om_zero] at hg; exact not_comp_zero g hg
    rw [Comp.eq_of_principal (SC_Om ha0).isPrincipal (Om_pos ha0).ne' hg] at hgC ⊢
    exact CSet.Om_mem (hlift a iha (mem_of_Om_mem hgC))
  | @coll π e hπ hπW _ _ hown_e ihπ ihe =>
    intro g hg hgC
    have hxSC := SC_psi hπ e
    rw [Comp.eq_of_principal hxSC.isPrincipal hxSC.1.ne' hg] at hgC ⊢
    by_cases hxq : S.psi e π < q
    · exact CSet.of_lt hxq
    have hqx : q ≤ S.psi e π := not_lt.1 hxq
    have hWx : Om (s + 1) ≤ S.psi e π := by
      rcases Ui.ui_psi_cases (S := S) (e := e) hs hπ hπW with h' | h'
      · exact absurd (h'.trans hLq) (not_lt.2 hqx)
      · exact h'
    by_cases hxV : S.psi B (Om (s + 1 + 1)) ≤ S.psi e π
    · obtain ⟨heC, heB⟩ := arg_mem_of_psi_mem hπ hgC hxV hVL hown_e
      have hπC : π ∈ C := by
        rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
        · exact CSet.I_mem _ _ n
        · have h1 := Om_mem_of_between hgC (psiS_bounds e t).1.le (psiS_bounds e t).2
          exact CSet.Om_mem (CSet.succ_mem (mem_of_Om_mem h1))
      exact CSet.psi_mem heB hπ (hlift π ihπ hπC) (hlift e ihe heC)
    · have hxlt : S.psi e π < S.psi B (Om (s + 1 + 1)) := not_le.1 hxV
      have hxVV : S.psi e π < Om (s + 1 + 1) := hxlt.trans (psi_lt hκV B)
      -- the subscript is `V`
      have hπV : π = Om (s + 1 + 1) := by
        rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
        · exfalso
          have hfix := Om_psiI (S := S) e n
          have h1 : Om (S.psi e (S.I n)) < Om (s + 1 + 1) := by rw [hfix]; exact hxVV
          have h2 : S.psi e (S.I n) < s + 1 + 1 := Om_lt_Om.1 h1
          have h3 : s + 1 < Om (s + 1) :=
            lt_of_le_of_ne (le_Om (s + 1)) (fun h => Om_ne_add_one (s + 1) s h.symm)
          exact absurd (Order.lt_add_one_iff.1 h2) (not_le.2 (h3.trans_le hWx))
        · have hb := psiS_bounds (S := S) e t
          have h1 : t < s + 1 + 1 := Om_lt_Om.1 (hb.1.trans hxVV)
          have h2 : s + 1 < t + 1 := Om_lt_Om.1 (hWx.trans_lt hb.2)
          have : t = s + 1 := le_antisymm (Order.lt_add_one_iff.1 h1)
            (Order.lt_add_one_iff.1 h2)
          rw [this]
      subst hπV
      have heB : e < B := lt_of_psi_lt hκV hown_e hown hxlt
      have heC : e ∈ C := (psi_mono hκV heB.le).2 hown_e
      exact CSet.psi_mem heB hκV (Ui.ui_W_mem (Ui.ui_s1_lt_omega hs) _ _) (hlift e ihe heC)

/-- **`K_q ∩ Cl(B, ψ_V(B)) ⊆ Cl(B, q)`** for `B` own at `V`, `L < q ≤ Λ`. -/
theorem uo_vis_mem (hs : s < ω) {B q x : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1))))
    (hLq : Om s < q) (hqL : q ≤ S.Lam) (hK : UlK S s q x) (hC : x ∈ S.CSet B (S.psi B (Om (s + 1 + 1)))) :
    x ∈ S.CSet B q :=
  uo_lift (fun g hg hx => uo_comp_mem x hx g hg) (uoG hs hown hLq x (uoK_of_K hqL hK)) hC

/-- **Downward visibility `Ul.UlDV S s` holds for every finite `s`.** -/
theorem uoDV (hs : s < ω) : UlDV S s := by
  intro B j hown hjK hjV
  have hle : S.psi B (Om (s + 1)) ≤ S.psi B (Om (s + 1 + 1)) := ul_psiW_le_psiV B B
  have hownV : B ∈ S.CSet B (S.psi B (Om (s + 1 + 1))) := CSet_mono le_rfl hle hown
  have hqL : S.psi B (Om (s + 1)) ≤ S.Lam :=
    ((Ui.ui_psi_lt B).trans (lt_Lam_of_mem zero_le (Ui.ui_W_mem (S := S) hs 0 0))).le
  exact uo_vis_mem hs hownV (Ui.ui_L_lt_psi B) hqL hjK (CSet.of_lt hjV)

/-- **Downward visibility at `s = 0`** (the levels of `ψ_{Ω₁}`), with no hypothesis. -/
theorem uoDV0 : UlDV S 0 := uoDV omega0_pos

/-- **FWD at every level `γ < V`**, with no hypothesis. -/
theorem uo_fwd (hs : s < ω) : ∀ γ : Ordinal.{0}, γ < Om (s + 1 + 1) → UlFWD S s γ :=
  ul_fwd hs (uoDV hs)

/-- **The lifted `ψ`-link at every level `γ < V`**, with no hypothesis: for an own `B` with `W^γ ∣ B`,
`γ ∈ Cl(B, ψ_W(B))`, `Hˡ_γ(c) = ψ_W(B)`, `D < W` with `d < Hˡ_γ(c + d)` for every `d ≤ D`:
`D < ψ_W(B + W^γ·D) = Hˡ_γ(c + D)`. -/
theorem uo_eq_all (hs : s < ω) {γ B c D : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB : Om (s + 1) ^ γ ∣ B)
    (hγB : γ ∈ S.CSet B (S.psi B (Om (s + 1)))) (hc : ulH S s γ c = S.psi B (Om (s + 1)))
    (hD : D < Om (s + 1)) (hcond : ∀ d, d ≤ D → d < ulH S s γ (c + d)) :
    D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧
      S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (c + D) :=
  ul_eq_all hs (uoDV hs) hγV hown hB hγB hc hD hcond

/-- **FWD for `Φ_μ := Hˡ_μ` at `s = 0` (the levels of `ψ_{Ω₁}`), every `μ < Ω₂`**, no hypothesis. -/
theorem uo_phi_fwd {μ : Ordinal.{0}} (hμ : μ < Om (0 + 1 + 1)) : UlFWD S 0 μ :=
  ul_phi_fwd (uoDV omega0_pos) hμ

/-- **The `ψ_{Ω₁} ↔ Φ_μ` link at every level `μ < Ω₂`**, no hypothesis. -/
theorem uo_phi_eq {μ B c D : Ordinal.{0}} (hμ : μ < Om (0 + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (0 + 1)))) (hB : Om (0 + 1) ^ μ ∣ B)
    (hμB : μ ∈ S.CSet B (S.psi B (Om (0 + 1)))) (hc : ulH S 0 μ c = S.psi B (Om (0 + 1)))
    (hD : D < Om (0 + 1)) (hcond : ∀ d, d ≤ D → d < ulH S 0 μ (c + d)) :
    D < S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) ∧
      S.psi (B + Om (0 + 1) ^ μ * D) (Om (0 + 1)) = ulH S 0 μ (c + D) :=
  uo_eq_all omega0_pos hμ hown hB hμB hc hD hcond

end Googology.Trans.PoR.InaccPsi.R2.Uo
