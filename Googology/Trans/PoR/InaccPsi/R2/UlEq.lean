import Googology.Trans.PoR.InaccPsi.R2.UlUB
import Googology.Trans.PoR.InaccPsi.R2.UiEq

/-!
# The `ψ_{Ω_{s+1}} ↔ Hˡ_γ` link at every lifted level `γ < Ω_{s+2}`, given downward visibility

`ψ = S.psi · W`, `ψ_V = S.psi · V`, `W = Ω_{s+1}`, `V = Ω_{s+2}`, `L = Ω_s`, `Hˡ_γ = ulH S s γ` (`R2.UlUB`), `K_q =
UlK S s q`, `ulD` the visibility datum (`R2.UlK`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.  A level `γ < V`
is visible at an own `B` when `γ ∈ Cl(B, ψ(B))`; then `γ < ψ_V(B)`: the `V`-part `A(γ)` of `B` sees every argument
of `γ`.  The one fact used about the levels below `γ` is the statement

  `UlDV S s` (**downward visibility**): for an own `B`, every `j ∈ K_{ψ(B)}` with `j < ψ_V(B)` lies in `Cl(B, ψ(B))`

(the arguments of a level below `ψ_V(B)` are below `B`).  For a level `j` of the notation, `Ul.ul_code_psi` gives
`j ∈ Cl(B, ψ(B))` from the normal-form datum `ulDat W j < ψ(B)` (the arguments of every `j < ψ_V(B)` of the notation
are below `B`, `Ul.ul_args_psi`); deriving it from `j ∈ K_{ψ(B)}` is left open.

* `ul_opow_mul_mem` (**`ω^x·y ∈ Cl(a, b)` for `x, y ∈ Cl(a, b)`**), `ul_Wpow_mem` (**`W^γ·D ∈ Cl(a, b)` for `γ, D ∈
  Cl(a, b)`**), `ul_supp_arg` (**support in the argument bound**: a member of `Cl(B, q)` lies in `Cl(A, q)` for some
  `A < B`, `A ∈ Cl(B, q)`, when `B` is closed under `+ 1`), `ul_lt_psiV` (a member of `Cl(a, b)` below `V`, `b ≤
  ψ_V(a)`, is below `ψ_V(a)`), `ul_K_of_mem` (`Cl(B, ψ(B)) ⊆ K_{ψ(B)}`);
* `UlDV`, `UlFWD` (the statements), `ul_fwd` (**FWD(γ) at every level `γ < V`**: `ψ(B)` is a fixed point of `Hˡ_γ`
  for every own `B ≠ 0` with `W^{γ+1} ∣ B` and `γ ∈ Cl(B, ψ(B))`, given `UlDV`; the own argument built below `ψ(B)`
  is moved above the rounding `M(A)` of the support `A` of `γ`);
* `ul_eq`, `ul_eq_all` (**`ψ(B + W^γ·D) = Hˡ_γ(c + D)` and `D < ψ(B + W^γ·D)`** for every level `γ < V`, own `B`
  with `W^γ ∣ B`, `γ ∈ Cl(B, ψ(B))`, `Hˡ_γ(c) = ψ(B)`, `D < W` with `d < Hˡ_γ(c + d)` for every `d ≤ D`, given
  `UlDV`).

No new axiom.  New definitions: the statement names `UlDV`, `UlFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## Hull facts -/

/-- `ω^h ∈ Cl(a, b)` gives `h ∈ Cl(a, b)`. -/
theorem ul_log_mem {a b h : Ordinal.{0}} (hm : ω ^ h ∈ S.CSet a b) : h ∈ S.CSet a b := by
  rcases eq_or_lt_of_le (right_le_opow h one_lt_omega0) with e | hlt
  · rw [e]; exact hm
  · have hv : veblen 0 h = ω ^ h := veblen_zero_apply h
    rw [← hv] at hm hlt
    exact (mem_of_veblen_mem hm (by rw [hv]; exact opow_pos h omega0_pos) hlt).2

/-- **`ω^x·y ∈ Cl(a, b)` for `x, y ∈ Cl(a, b)`.** -/
theorem ul_opow_mul_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) :
    ∀ y, y ∈ S.CSet a b → ω ^ x * y ∈ S.CSet a b := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hy hy0
  have hh : log ω y ∈ S.CSet a b := ul_log_mem hl
  have e : ω ^ x * y = ω ^ (x + log ω y) + ω ^ x * tail y := by
    conv_lhs => rw [← lead_add_tail hy0]
    rw [mul_add, lead, ← opow_add]
  rw [e]
  have h1 : ω ^ (x + log ω y) ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem a b) (CSet.add_mem hx hh); rwa [veblen_zero_apply] at this
  exact CSet.add_mem h1 (IH _ (tail_lt hy0) ht)

/-- **`W^γ·D ∈ Cl(a, b)` for `γ, D ∈ Cl(a, b)`.** -/
theorem ul_Wpow_mem (hs : s < ω) {a b γ D : Ordinal.{0}} (hγ : γ ∈ S.CSet a b) (hD : D ∈ S.CSet a b) :
    Om (s + 1) ^ γ * D ∈ S.CSet a b := by
  have hWγ : Om (s + 1) * γ ∈ S.CSet a b := by
    have := ul_opow_mul_mem (Ui.ui_W_mem (S := S) hs a b) γ hγ; rwa [Ui.ui_W_opow s] at this
  rw [Ui.ui_W_eq s]; exact ul_opow_mul_mem hWγ D hD

theorem ul_max_mem {C : Set Ordinal.{0}} {x y : Ordinal.{0}} (hx : x ∈ C) (hy : y ∈ C) : max x y ∈ C := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]; exact hy
  · rw [max_eq_left h]; exact hx

/-- **Support in the argument bound**: every member of `Cl(B, q)` lies in `Cl(A, q)` for some `A < B` with `A ∈
Cl(B, q)`, when `B` is closed under `+ 1` and `0 < B`. -/
theorem ul_supp_arg {B q : Ordinal.{0}} (hB0 : 0 < B) (hB1 : ∀ e, e < B → e + 1 < B) :
    ∀ x, x ∈ S.CSet B q → ∃ A, A < B ∧ A ∈ S.CSet B q ∧ x ∈ S.CSet A q := by
  have h0 : (0 : Ordinal.{0}) ∈ S.CSet B q := CSet.zero_mem _ _
  have hmono : ∀ {A A' z : Ordinal.{0}}, A ≤ A' → z ∈ S.CSet A q → z ∈ S.CSet A' q :=
    fun hAA hz => CSet_mono hAA le_rfl hz
  intro x hx
  induction hx with
  | small h => exact ⟨0, hB0, h0, CSet.of_lt h⟩
  | zero => exact ⟨0, hB0, h0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, hB0, h0, CSet.I_mem _ _ n⟩
  | inaccW => exact ⟨0, hB0, h0, CSet.Iw_mem _ _⟩
  | add _ _ ihx ihy =>
    obtain ⟨A1, h1, m1, k1⟩ := ihx
    obtain ⟨A2, h2, m2, k2⟩ := ihy
    exact ⟨max A1 A2, max_lt h1 h2, ul_max_mem m1 m2,
      CSet.add_mem (hmono (le_max_left _ _) k1) (hmono (le_max_right _ _) k2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨A1, h1, m1, k1⟩ := ihx
    obtain ⟨A2, h2, m2, k2⟩ := ihy
    exact ⟨max A1 A2, max_lt h1 h2, ul_max_mem m1 m2,
      CSet.phi_mem (hmono (le_max_left _ _) k1) (hmono (le_max_right _ _) k2)⟩
  | om _ ih =>
    obtain ⟨A1, h1, m1, k1⟩ := ih
    exact ⟨A1, h1, m1, CSet.Om_mem k1⟩
  | @coll π e hπ _ heC ihπ ihe =>
    obtain ⟨A1, h1, m1, k1⟩ := ihπ
    obtain ⟨A2, h2, m2, k2⟩ := ihe
    have he1 : e.1 + 1 < B := hB1 e.1 e.2
    have hm3 : e.1 + 1 ∈ S.CSet B q := CSet.succ_mem heC
    refine ⟨max (max A1 A2) (e.1 + 1), max_lt (max_lt h1 h2) he1, ul_max_mem (ul_max_mem m1 m2) hm3, ?_⟩
    show S.psi e.1 π ∈ S.CSet (max (max A1 A2) (e.1 + 1)) q
    exact CSet.psi_mem ((lt_add_one e.1).trans_le (le_max_right _ _)) hπ
      (hmono ((le_max_left _ _).trans (le_max_left _ _)) k1)
      (hmono ((le_max_right _ _).trans (le_max_left _ _)) k2)

/-- A member of `Cl(a, b)` below `V`, with `b ≤ ψ_V(a')`, `a ≤ a'`, is below `ψ_V(a')`. -/
theorem ul_lt_psiV {a a' b γ : Ordinal.{0}} (hγ : γ ∈ S.CSet a b) (haa : a ≤ a')
    (hb : b ≤ S.psi a' (Om (s + 1 + 1))) (hγV : γ < Om (s + 1 + 1)) : γ < S.psi a' (Om (s + 1 + 1)) :=
  lt_psi_of_mem (InR_Om_succ (s + 1)) (CSet_mono haa hb hγ) hγV

/-- `ψ_W(e) ≤ ψ_V(e')` for every `e`, `e'`. -/
theorem ul_psiW_le_psiV (e e' : Ordinal.{0}) : S.psi e (Om (s + 1)) ≤ S.psi e' (Om (s + 1 + 1)) :=
  (Ui.ui_psi_lt e).le.trans (psiS_bounds e' (s + 1)).1.le

/-- **`Cl(B, ψ(B)) ⊆ K_{ψ(B)}`.** -/
theorem ul_K_of_mem {B x : Ordinal.{0}} (hx : x ∈ S.CSet B (S.psi B (Om (s + 1)))) :
    UlK S s (S.psi B (Om (s + 1))) x := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  exact ulK_hull (fun e he heC _ => lt_psi_of_mem hκ (CSet.psi_mem he hκ (mem_CSet_psi hκ B) heC)
    (Ui.ui_psi_lt e)) x hx

/-! ## Downward visibility and FWD -/

/-- **Downward visibility** (a statement name): for an own `B`, every level `j ∈ K_{ψ(B)}` with `j < ψ_V(B)` lies in
`Cl(B, ψ(B))`. -/
def UlDV (S : InaccSeq.{0}) (s : Ordinal.{0}) : Prop :=
  ∀ B j : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (s + 1))) → UlK S s (S.psi B (Om (s + 1))) j →
    j < S.psi B (Om (s + 1 + 1)) → j ∈ S.CSet B (S.psi B (Om (s + 1)))

/-- **FWD(γ)**: `ψ(B)` is a fixed point of `Hˡ_γ` for every own `B ≠ 0` with `W^{γ+1} ∣ B` and `γ ∈ Cl(B, ψ(B))`. -/
def UlFWD (S : InaccSeq.{0}) (s γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (s + 1))) → Om (s + 1) ^ (γ + 1) ∣ B → B ≠ 0 →
    γ ∈ S.CSet B (S.psi B (Om (s + 1))) → ulH S s γ (S.psi B (Om (s + 1))) = S.psi B (Om (s + 1))

/-- **FWD(γ) at every level `γ < V`**, given downward visibility. -/
theorem ul_fwd (hs : s < ω) (hDV : UlDV S s) : ∀ γ : Ordinal.{0}, γ < Om (s + 1 + 1) → UlFWD S s γ := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hE0 : (0 : Ordinal.{0}) < Ui.uiE s := (Ui.ui_SC_W s).1.trans (Ui.uiE_gt s)
  have hWL : Om (s + 1) < S.Lam := lt_Lam_of_mem zero_le (Ui.ui_W_mem (S := S) hs 0 0)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγV B hown hB hB0 hγB
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [ulH_eq_uiH hs hE0]
    exact Ui.ui_fix0 hs hown (by rwa [zero_add, opow_one] at hB) hB0
  set x := S.psi B (Om (s + 1)) with hxdef
  have hx2 : x < Om (s + 1) := Ui.ui_psi_lt B
  have hxSC : SC x := Ui.ui_psi_SC B
  have hx1 : Om s < x := Ui.ui_L_lt_psi B
  have hxΓ : ulH S s 0 x = x := by
    have h1 : Om (s + 1) ^ ((0 : Ordinal.{0}) + 1) ∣ B :=
      (opow_dvd_opow _ (by rw [zero_add]; exact le_add_self)).trans hB
    exact IH 0 (pos_iff_ne_zero.2 hγ0) ((pos_iff_ne_zero.2 hγ0).trans hγV) B hown h1 hB0 (CSet.zero_mem _ _)
  have hlimx : IsSuccLimit x := hxSC.isSuccLimit
  set u := Om (s + 1) ^ γ with hudef
  have hu0 : u ≠ 0 := (Ui.ui_W_pos s γ).ne'
  have hupos : 0 < u := Ui.ui_W_pos s γ
  have hWB : Om (s + 1) ∣ B := by
    have : Om (s + 1) ^ (1 : Ordinal.{0}) ∣ B := (opow_dvd_opow _ le_add_self).trans hB
    rwa [opow_one] at this
  obtain ⟨m, hm⟩ := hB
  rw [Ui.ui_W_succ s, ← hudef, mul_assoc] at hm
  have hγK : UlK S s x γ := ul_K_of_mem hγB
  have hCx : ulD S s γ < x := (ul_vis hxSC).2 hγK
  -- the support `A` of `γ` in the argument bound, and its rounding `M(A)`
  have hB1 : ∀ e, e < B → e + 1 < B := fun e he =>
    Rd.rd_add_lt_of_dvd (Ui.ui_W_indec' s) hWB he (Ui.ui_one_lt_W s)
  obtain ⟨A, hAB, hAmem, hγA⟩ := ul_supp_arg (pos_iff_ne_zero.2 hB0) hB1 γ hγB
  have hAL : A < S.Lam := lt_Lam_of_mem (hx2.trans hWL).le hAmem
  set Ma := S.M A (S.psi A (Om (s + 1))) A with hMadef
  have hMaown : Ma ∈ S.CSet Ma (S.psi Ma (Om (s + 1))) := M_mem_self hκ hAL
  have hψMa : S.psi Ma (Om (s + 1)) = S.psi A (Om (s + 1)) := psi_M_eq hκ hAL
  have hAMa : A ≤ Ma := (M_spec hAL).2
  have hψA : S.psi A (Om (s + 1)) < x := psi_lt_psi_of_mem hκ hAB hAmem
  have hMaB : Ma < B := (Ui.ui_own_lt_iff hMaown hown).1 (by rw [hψMa]; exact hψA)
  have hγψA : γ < S.psi A (Om (s + 1 + 1)) := ul_lt_psiV hγA le_rfl (ul_psiW_le_psiV B A) hγV
  have key : ∀ z < x, ulH S s γ z < x := by
    intro z hz
    have hxI : Indec x := Lq.lq_SC_indec hxSC
    set a := Om s + ulD S s γ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt (hxI.add_lt (hxI.add_lt hx1 hCx) hz)
    set p := ulH S s 0 a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact (ulH_lt_iff (S := S) (s := s) 0).2 hax
    have hpSC : SC p := ulH_SC (S := S) (s := s) 0 a
    have hap : a < p := by
      rw [hpdef, ulH_eq_uiH hs hE0]; exact Ui.uiH_zero_lt _
    have hCp : ulD S s γ < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef]; exact le_add_self.trans (le_self_add.trans le_self_add)
    have hz1p : z + 1 < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef, add_assoc]; exact le_add_self
    have hp1 : Om s < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef]; exact le_self_add.trans (le_self_add.trans le_self_add)
    obtain ⟨Bp, hownp, hBpB, hpBp, -⟩ := Ui.ui_own_below_lt hs hown hpSC hp1 hpx
    set E := max Bp Ma with hEdef
    have hownE : E ∈ S.CSet E (S.psi E (Om (s + 1))) := by
      rcases le_total Bp Ma with h | h
      · rw [hEdef, max_eq_right h]; exact hMaown
      · rw [hEdef, max_eq_left h]; exact hownp
    have hEB : E < B := max_lt hBpB hMaB
    have hAE : A ≤ E := hAMa.trans (le_max_right _ _)
    have hpE : p ≤ S.psi E (Om (s + 1)) := hpBp.trans (psi_mono hκ (le_max_left Bp Ma)).1
    set e := u * (E / u) + u with hedef
    have hEe : E ≤ e := by
      calc E = u * (E / u) + E % u := (Ordinal.div_add_mod E u).symm
        _ ≤ e := add_le_add_right (Ordinal.mod_lt E hu0).le _
    have hpe : p ≤ S.psi e (Om (s + 1)) := hpE.trans (psi_mono hκ hEe).1
    have hCe : ulD S s γ < S.psi e (Om (s + 1)) := hCp.trans_le hpe
    -- `γ` is visible at `E` (downward visibility), hence at `e`
    have hγE : γ ∈ S.CSet E (S.psi E (Om (s + 1))) :=
      hDV E γ hownE ((ul_vis (Ui.ui_psi_SC E)).1 (hCp.trans_le hpE)) (hγψA.trans_le (psi_mono hκV hAE).1)
    have hEmem : E ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hEe).2 hownE
    have hγe : γ ∈ S.CSet e (S.psi e (Om (s + 1))) := (psi_mono hκ hEe).2 hγE
    have hmod : u * (E / u) ∈ S.CSet e (S.psi e (Om (s + 1))) :=
      Ui.ui_mod_mem (S := S) (one_le_iff_ne_zero.2 hγ0) E hEmem
    have huM : u ∈ S.CSet e (S.psi e (Om (s + 1))) := by
      have := ul_Wpow_mem (S := S) hs hγe (CSet.one_mem _ _); rwa [mul_one] at this
    have howne : e ∈ S.CSet e (S.psi e (Om (s + 1))) := CSet.add_mem hmod huM
    have hue : u ∣ e := ⟨E / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hγψe : ∀ d, γ < S.psi (e + u * d) (Om (s + 1 + 1)) := fun d =>
      hγψA.trans_le (psi_mono hκV (hAE.trans (hEe.trans le_self_add))).1
    have hed : ∀ d, d < S.psi e (Om (s + 1)) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (s + 1))) ∧
          ∃ w, ulH S s γ w = S.psi (e + u * d) (Om (s + 1)) := by
      intro d hd
      have hle : S.psi e (Om (s + 1)) ≤ S.psi (e + u * d) (Om (s + 1)) := (psi_mono hκ le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (s + 1))) :=
        CSet.add_mem ((psi_mono hκ le_self_add).2 howne)
          (ul_Wpow_mem hs ((psi_mono hκ le_self_add).2 hγe) (CSet.of_lt (hd.trans_le hle)))
      refine ⟨hownd, ucG_range (Ui.ui_psi_SC _) (Ui.ui_L_lt_psi _) (hCe.trans_le hle) fun j hj hcj => ?_⟩
      have hjvis : j ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (s + 1))) :=
        hDV _ j hownd ((ul_vis (Ui.ui_psi_SC _)).1 hcj) (hj.trans (hγψe d))
      exact IH j hj (hj.trans hγV) _ hownd
        ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hjvis
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om (s + 1)) →
        S.psi (e + u * d) (Om (s + 1)) < S.psi (e + u * d') (Om (s + 1)) := fun d d' hdd hd' =>
      Ui.ui_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om (s + 1)) → ∀ w, ulH S s γ w = S.psi (e + u * d) (Om (s + 1)) →
        d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : ulH S s γ w' < ulH S s γ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((ulH_lt_iff (S := S) (s := s) γ).1 h2) (not_lt.2 h1)
    have hz1e : z + 1 < S.psi e (Om (s + 1)) := hz1p.trans_le hpe
    obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
    have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
    have hlt : e + u * (z + 1) < B := by
      have hq : E / u < Om (s + 1) * m := by
        rw [hm] at hEB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hEB
      have hc1 : 1 + (z + 1) < Om (s + 1) :=
        (Lq.lq_SC_indec (Ui.ui_SC_W s)).add_lt (Ui.ui_one_lt_W s) ((Ui.ui_SC_W s).add_one_lt (hz.trans hx2))
      have e1 : e + u * (z + 1) = u * (E / u + (1 + (z + 1))) := by
        simp only [hedef, mul_add, mul_one, add_assoc]
      rw [e1, hm]
      exact (mul_lt_mul_iff_right₀ hupos).2
        (Rd.rd_add_lt_of_dvd (Lq.lq_SC_indec (Ui.ui_SC_W s)) (dvd_mul_right _ _) hq hc1)
    have hψlt : S.psi (e + u * (z + 1)) (Om (s + 1)) < x :=
      psi_lt_psi_of_mem hκ hlt ((psi_mono hκ hlt.le).2 (hed (z + 1) hz1e).1)
    calc ulH S s γ z < ulH S s γ w := (ulH_lt_iff (S := S) (s := s) γ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((ulH_normal (S := S) (s := s) γ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (ulH_le_self (S := S) (s := s) γ x)

/-! ## The link -/

/-- **`ψ(B + W^γ·D) = Hˡ_γ(c + D)`, and `D < ψ(B + W^γ·D)`**, at a level `γ < V` visible at the own `B`, `W^γ ∣ B`,
`Hˡ_γ(c) = ψ(B)`, `D < W` with `d < Hˡ_γ(c + d)` for every `d ≤ D`, given downward visibility. -/
theorem ul_eq (hs : s < ω) (hDV : UlDV S s) {γ : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB : Om (s + 1) ^ γ ∣ B)
    (hγB : γ ∈ S.CSet B (S.psi B (Om (s + 1)))) (hc : ulH S s γ c = S.psi B (Om (s + 1))) :
    ∀ D, D < Om (s + 1) → (∀ d, d ≤ D → d < ulH S s γ (c + d)) →
      D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧
        S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (c + D) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  set u := Om (s + 1) ^ γ with hudef
  have hupos : 0 < u := Ui.ui_W_pos s γ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om (s + 1)) = ulH S s γ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om (s + 1)) = ulH S s γ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om (s + 1)) with hv
    have hvSC : SC v := Ui.ui_psi_SC _
    have hBv : S.psi B (Om (s + 1)) < v :=
      Ui.ui_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hCv : ulD S s γ < v := (ulH_D_lt (S := S) (s := s) γ c).trans (hc ▸ hBv)
    have hγv : γ ∈ S.CSet (B + u * D) v := CSet_mono le_self_add hBv.le hγB
    have hlt : ∀ d, d < D → ulH S s γ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om (s + 1)) ≤ v :=
        (psi_mono (S := S) hκ ((add_le_add_iff_left B).2 (mul_le_mul_right hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * D)).2 hown)
          (ul_Wpow_mem hs hγv (CSet.of_lt hdv))
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact ulUB hs γ B c D hB hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ hγv ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (ul_Wpow_mem hs hγv (CSet.of_lt hDv))
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hγψ : γ < S.psi (B + u * (d0 + 1)) (Om (s + 1 + 1)) :=
          ul_lt_psiV hγB le_self_add (ul_psiW_le_psiV _ _) hγV
        have hfix : ∀ j < γ, ulD S s j < v → ucG (ulD S s) (Om s) j v = v := fun j hj hcj =>
          ul_fwd hs hDV j (hj.trans hγV) _ hown1 ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans
            (dvd_add hB (dvd_mul_right _ _))) hne (hDV _ j hown1 ((ul_vis hvSC).1 hcj) (hj.trans hγψ))
        obtain ⟨e, he⟩ := ucG_range (d := ulD S s) (L := Om s) hvSC (Ui.ui_L_lt_psi _) hCv hfix
        have hle' : c + (d0 + 1) ≤ e := by
          refine not_lt.1 fun hlt' => ?_
          have hle : e ≤ c + d0 := by
            rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
          have := ((ucG_le_iff (d := ulD S s) (L := Om s) γ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
          rw [he] at this
          exact lt_irrefl _ this
        calc ulH S s γ (c + (d0 + 1)) ≤ ucG (ulD S s) (Om s) γ e :=
              (ucG_le_iff (d := ulD S s) (L := Om s) γ).2 hle'
          _ = v := he
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((ulH_normal (S := S) (s := s) γ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : ulH S s γ e < v :=
            ((ulH_lt_iff (S := S) (s := s) γ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **The `ψ_{Ω_{s+1}} ↔ Hˡ_γ` link at every lifted level `γ < Ω_{s+2}`**, given downward visibility. -/
theorem ul_eq_all (hs : s < ω) (hDV : UlDV S s) {γ B c D : Ordinal.{0}} (hγV : γ < Om (s + 1 + 1))
    (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (hB : Om (s + 1) ^ γ ∣ B)
    (hγB : γ ∈ S.CSet B (S.psi B (Om (s + 1)))) (hc : ulH S s γ c = S.psi B (Om (s + 1)))
    (hD : D < Om (s + 1)) (hcond : ∀ d, d ≤ D → d < ulH S s γ (c + d)) :
    D < S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) ∧
      S.psi (B + Om (s + 1) ^ γ * D) (Om (s + 1)) = ulH S s γ (c + D) :=
  ul_eq hs hDV hγV hown hB hγB hc D hD hcond

end Googology.Trans.PoR.InaccPsi.R2.Ul
