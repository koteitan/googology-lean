import Googology.Trans.PoR.InaccPsi.R2.UeTerm
import Googology.Trans.PoR.InaccPsi.R2.SiUnc
import Googology.Trans.PoR.InaccPsi.R2.RjFacts
import Googology.Trans.PoR.InaccPsi.R2.CitedUh

/-!
# Terms with uncountable `ϑ`-arguments `Ω₁·M + ρ` at every code level `M < ε_{Ω₁+1}` with small data

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`UhT` is `Ue.UeT` with the node `thc M r` (value `ϑᵗ(Ω₁·M + r)`, `r` countable) at every **level** `M` with
`UhLev κ M`: `1 ≤ M < ε_{Ω₁+1}` and `rjDat M < κ` (`Rj.rjDat`: the largest countable leaf of the hereditary Cantor
normal form of `M` over `{0, Ω₁}`; `rjDat M = M` for `M < Ω₁`, so the constant levels `1 ≤ q < κ` of `Ue.UeT` are
the levels `M < Ω₁`).  `κ` is a fixed `ε`-number below every base.  `ev`, `map`, `Lv`, `WF`, `Nd`, `tr` as in
`Ue.UeT` (the levels are constants: `π`, the segment moves and the translations fix `Ω₁·M`).

* `uh_pi_fix` (**`M ∈ Tᵗ[σ]`, `π_{σ,τ}(M) = M` for `M < ε_{Ω₁+1}`, `rjDat M < σ`**), `uh_Om1_mul_TB` (**the same for
  `Ω₁·M`**; from the cited `R2.om1_opow_TB_all` through `R2.siOm1_opow_TB`, `R2.pi_add`, `R2.pi_Om1`);
* `uhMem`, `uhLe` (**every leaf and every `thc`-value is `≤` the value**: `R2.luLt_vt_self` for `M < Ω₁`,
  `R2.rjLevel_lt_vt` for `M ≥ Ω₁`); `uhDown`, `uhUp`, `uhUp_eq`, `uhMv` (**base change and segment move on terms**);
* `uhTrA`, `uhTrB` (**the translations `t^α_τ`, `t^τ_α` of [W07a] Def 6.2 are correct**, from `R2.uhVt_tr`);
* `uhVt_tr_ue` (**`R2.ueVt_tr` is the case `M < Ω₁` of `R2.uhVt_tr`**);
* `ofUe` (**`Ue.UeT` embeds**: `ofUe_ev`, `ofUe_map`, `ofUe_WF`, `ofUe_Lv`, `ofUe_Qs` for `κ ≤ Ω₁`), `ofUb`.

New definitions: `UhLev`, `UhT`, `ev`, `map`, `Lv`, `Qs`, `WF`, `Nd`, `tr`, `ofUe`, `ofUb`, `lvq`, `lvs`.  No new
axiom (uses `R2.uhVt_tr`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uh

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- **A level over `κ`**: `1 ≤ M < ε_{Ω₁+1}` with countable data `rjDat M < κ`. -/
def UhLev (κ M : Ordinal.{0}) : Prop := 1 ≤ M ∧ M < Gg.ggE ∧ Rj.rjDat M < κ

theorem UhLev.mono {κ κ' M : Ordinal.{0}} (hκ : κ ≤ κ') (h : UhLev κ M) : UhLev κ' M :=
  ⟨h.1, h.2.1, h.2.2.trans_le hκ⟩

/-- Terms over a base: parameters, `+`, `ϑᵗ(0)`, `ϑᵗ(1 + ξ)`, `ϑᵗ(Ω₁·M + ρ)`. -/
inductive UhT : Type 1
  | par : Ordinal.{0} → UhT
  | add : UhT → UhT → UhT
  | base : UhT
  | th1 : UhT → UhT
  | thc : Ordinal.{0} → UhT → UhT

namespace UhT

instance : Inhabited UhT := ⟨UhT.base⟩

/-- Evaluation over the base `τ`. -/
noncomputable def ev (τ : Ordinal.{0}) : UhT → Ordinal.{0}
  | par p => p
  | add s t => ev τ s + ev τ t
  | base => τ
  | th1 s => vt τ (1 + ev τ s)
  | thc q r => vt τ (Om1 * q + ev τ r)

/-- Apply `f` to every leaf (the levels `q` are constants). -/
def map (f : Ordinal.{0} → Ordinal.{0}) : UhT → UhT
  | par p => par (f p)
  | add s t => add (map f s) (map f t)
  | base => base
  | th1 s => th1 (map f s)
  | thc q r => thc q (map f r)

/-- Every leaf satisfies `P`. -/
def Lv (P : Ordinal.{0} → Prop) : UhT → Prop
  | par p => P p
  | add s t => Lv P s ∧ Lv P t
  | base => True
  | th1 s => Lv P s
  | thc _ r => Lv P r

/-- Every level `M` of a `thc`-node is a level over `κ` (`UhLev κ M`). -/
def Qs (κ : Ordinal.{0}) : UhT → Prop
  | par _ => True
  | add s t => Qs κ s ∧ Qs κ t
  | base => True
  | th1 s => Qs κ s
  | thc q r => UhLev κ q ∧ Qs κ r

/-- The argument bounds over `τ`: the arguments of `th1` and the countable parts of `thc` are `< Ω₁`. -/
def WF (τ : Ordinal.{0}) : UhT → Prop
  | par _ => True
  | add s t => WF τ s ∧ WF τ t
  | base => True
  | th1 s => WF τ s ∧ ev τ s < Om1
  | thc _ r => WF τ r ∧ ev τ r < Om1

/-- Every `thc`-node value over `τ` satisfies `P`. -/
def Nd (τ : Ordinal.{0}) (P : Ordinal.{0} → Prop) : UhT → Prop
  | par _ => True
  | add s t => Nd τ P s ∧ Nd τ P t
  | base => True
  | th1 s => Nd τ P s
  | thc q r => P (vt τ (Om1 * q + ev τ r)) ∧ Nd τ P r

/-- The translation `t^a_b` of [W07a] Def 6.2 (`ϑ^a(0) ↦ a`, `ϑ^a(1 + ξ) ↦ ϑ^b(1 + a + ξ)`,
`ϑ^a(Ω₁·M + ρ) ↦ ϑ^b(Ω₁·M + a + ρ)`). -/
def tr (a : Ordinal.{0}) : UhT → UhT
  | par p => par p
  | add s t => add (tr a s) (tr a t)
  | base => par a
  | th1 s => th1 (add (par a) (tr a s))
  | thc q r => thc q (add (par a) (tr a r))

theorem Lv_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) : ∀ t : UhT, Lv P t → Lv Q t
  | par p, h => hPQ p h
  | add s t, h => ⟨Lv_mono hPQ s h.1, Lv_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_mono hPQ s h
  | thc _ r, h => Lv_mono hPQ r h

theorem Nd_mono {τ : Ordinal.{0}} {P Q : Ordinal.{0} → Prop} (hPQ : ∀ p, P p → Q p) :
    ∀ t : UhT, Nd τ P t → Nd τ Q t
  | par _, _ => trivial
  | add s t, h => ⟨Nd_mono hPQ s h.1, Nd_mono hPQ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Nd_mono hPQ s h
  | thc _ r, h => ⟨hPQ _ h.1, Nd_mono hPQ r h.2⟩

theorem Qs_mono {κ κ' : Ordinal.{0}} (hκ : κ ≤ κ') : ∀ t : UhT, Qs κ t → Qs κ' t
  | par _, _ => trivial
  | add s t, h => ⟨Qs_mono hκ s h.1, Qs_mono hκ t h.2⟩
  | base, _ => trivial
  | th1 s, h => Qs_mono hκ s h
  | thc _ r, h => ⟨h.1.mono hκ, Qs_mono hκ r h.2⟩

theorem map_map (f g : Ordinal.{0} → Ordinal.{0}) : ∀ t : UhT, (t.map g).map f = t.map (f ∘ g)
  | par _ => rfl
  | add s t => by simp only [map, map_map f g s, map_map f g t]
  | base => rfl
  | th1 s => by simp only [map, map_map f g s]
  | thc _ r => by simp only [map, map_map f g r]

theorem map_congr {f g : Ordinal.{0} → Ordinal.{0}} : ∀ t : UhT, Lv (fun p => f p = g p) t → t.map f = t.map g
  | par _, h => by simp only [map]; rw [show _ = _ from h]
  | add s t, h => by simp only [map, map_congr s h.1, map_congr t h.2]
  | base, _ => rfl
  | th1 s, h => by simp only [map, map_congr s h]
  | thc _ r, h => by simp only [map, map_congr r h]

theorem map_id : ∀ t : UhT, t.map id = t
  | par _ => rfl
  | add s t => by simp only [map, map_id s, map_id t]
  | base => rfl
  | th1 s => by simp only [map, map_id s]
  | thc _ r => by simp only [map, map_id r]

theorem Lv_and {P Q : Ordinal.{0} → Prop} : ∀ (t : UhT), Lv P t → Lv Q t → Lv (fun p => P p ∧ Q p) t
  | par _, h1, h2 => ⟨h1, h2⟩
  | add s t, h1, h2 => ⟨Lv_and s h1.1 h2.1, Lv_and t h1.2 h2.2⟩
  | base, _, _ => trivial
  | th1 s, h1, h2 => Lv_and s h1 h2
  | thc _ r, h1, h2 => Lv_and r h1 h2

theorem Lv_map {P : Ordinal.{0} → Prop} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ t : UhT, Lv (fun p => P (f p)) t → Lv P (t.map f)
  | par _, h => h
  | add s t, h => ⟨Lv_map s h.1, Lv_map t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_map s h
  | thc _ r, h => Lv_map r h

theorem Qs_map {κ : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : UhT, Qs κ t → Qs κ (t.map f)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_map f s h.1, Qs_map f t h.2⟩
  | base, _ => trivial
  | th1 s, h => Qs_map f s h
  | thc _ r, h => ⟨h.1, Qs_map f r h.2⟩

theorem tr_map (a : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ t : UhT, (tr a t).map f = tr (f a) (t.map f)
  | par _ => rfl
  | add s t => by simp only [tr, map, tr_map a f s, tr_map a f t]
  | base => rfl
  | th1 s => by simp only [tr, map, tr_map a f s]
  | thc _ r => by simp only [tr, map, tr_map a f r]

theorem Qs_tr {κ : Ordinal.{0}} (a : Ordinal.{0}) : ∀ t : UhT, Qs κ t → Qs κ (tr a t)
  | par _, _ => trivial
  | add s t, h => ⟨Qs_tr a s h.1, Qs_tr a t h.2⟩
  | base, _ => trivial
  | th1 s, h => ⟨trivial, Qs_tr a s h⟩
  | thc _ r, h => ⟨h.1, trivial, Qs_tr a r h.2⟩

theorem Lv_tr {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (ha : P a) : ∀ t : UhT, Lv P t → Lv P (tr a t)
  | par _, h => h
  | add s t, h => ⟨Lv_tr ha s h.1, Lv_tr ha t h.2⟩
  | base, _ => ha
  | th1 s, h => ⟨ha, Lv_tr ha s h⟩
  | thc _ r, h => ⟨ha, Lv_tr ha r h⟩

/-- The leaves of `tr a t` are those of `t` and `a`. -/
theorem Lv_tr_inv {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} : ∀ t : UhT, Lv P (tr a t) → Lv P t
  | par _, h => h
  | add s t, h => ⟨Lv_tr_inv s h.1, Lv_tr_inv t h.2⟩
  | base, _ => trivial
  | th1 s, h => Lv_tr_inv s h.2
  | thc _ r, h => Lv_tr_inv r h.2

end UhT

open UhT

/-! ## Membership and the order of the parts -/

/-- A countable ordinal below an `ε`-number base `τ` lies in `Tᵗ`; so does `τ` ([W07b] Cor 5.10, `T_inter_Om1`). -/
theorem uh_T_le {τ x : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hx : x ≤ τ) : x ∈ Tset τ := by
  obtain ⟨m, hm, -, -, hT⟩ := T_inter_Om1 hτ hτ1
  exact (hT x (hx.trans_lt hτ1)).2 (hx.trans_lt hm)

/-- **`M ∈ Tᵗ[σ]` and `π_{σ,τ}(M) = M`** for `M < ε_{Ω₁+1}` with `rjDat M < σ` (induction on `M`: `M < Ω₁` is a
parameter `< σ`; `M = Ω₁`: `pi_Om1`; `Ω₁ < M = ω^l·v + r` (`l = log_ω M ≥ Ω₁`, `v < ω`, `r < ω^l`), `ω^l = Ω₁·ω^b`
with `l = Ω₁ + b`, `rjDat b ≤ rjDat l ≤ rjDat M`; `siOm1_opow_TB` (from the cited `om1_opow_TB_all`) and
`pi_add`). -/
theorem uh_pi_fix {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ M, M < Gg.ggE → Rj.rjDat M < σ → M ∈ TB τ σ ∧ pi σ τ M = M := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hME hMd
  rcases lt_trichotomy M Om1 with hM1 | rfl | hM1
  · rw [Rj.rjDat_small hM1] at hMd
    exact ⟨mem_TB_of_lt h hMd, pi_lt h hMd⟩
  · exact pi_Om1 h
  · have hM0 : M ≠ 0 := (lt_of_le_of_lt zero_le hM1).ne'
    obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hM0
    set l := log ω M with hldef
    set v := M / ω ^ l with hvdef
    set r := M % ω ^ l with hrdef
    have hM1' : Om1 < ω ^ l * v + r := by rw [hdec]; exact hM1
    have hME' : ω ^ l * v + r < Gg.ggE := by rw [hdec]; exact hME
    have hdat : Rj.rjDat M = max (Rj.rjDat l) (Rj.rjDat r) := by
      rw [← Si.si_rjDat_form hv0 hvω hr hM1' hME', hdec]
    have hlM : l < M := Rj.rj_log_lt hM1 hME
    have hl1 : Om1 ≤ l := Rj.rj_lead_lt hM1
    have hrM : r < M := hr.trans_le (opow_log_le_self ω hM0)
    have hdl : Rj.rjDat l < σ := (le_max_left _ _).trans_lt (hdat ▸ hMd)
    have hdr : Rj.rjDat r < σ := (le_max_right _ _).trans_lt (hdat ▸ hMd)
    -- `ω^l = Ω₁·ω^b`
    set b := l - Om1 with hbdef
    have hlb : Om1 + b = l := Ordinal.add_sub_cancel_of_le hl1
    have hbl : b ≤ l := by rw [← hlb]; exact le_add_self
    have hbM : b < M := hbl.trans_lt hlM
    have hdb : Rj.rjDat b ≤ Rj.rjDat l := by
      rcases eq_or_ne b 0 with hb0 | hb0
      · rw [hb0, Rj.rjDat_small Rj.rj_Om1_pos]; exact zero_le
      · rcases lt_or_ge b Om1 with hbO | hbO
        · rw [← hlb, Rj.rjDat_Om1_add hb0 hbO, Rj.rjDat_small hbO]
        · rw [← hlb, Si.si_rjDat_Om1_add hbO (hbM.trans hME)]
    obtain ⟨hbT, hbπ⟩ := IH b hbM (hbM.trans hME) (hdb.trans_lt hdl)
    have hwl : ω ^ l = Om1 * ω ^ b := by rw [Si.si_Om1_opow_eq, hlb]
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h (hbM.trans hME)
    have hwT : ω ^ l ∈ TB τ σ ∧ pi σ τ (ω ^ l) = ω ^ l := by
      rw [hwl]; exact ⟨o1.2 hbT, by rw [o2 hbT, hbπ]⟩
    -- `ω^l·v`
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
    have hmul : ∀ k : ℕ, ω ^ l * (k : Ordinal.{0}) ∈ TB τ σ ∧
        pi σ τ (ω ^ l * (k : Ordinal.{0})) = ω ^ l * (k : Ordinal.{0}) := by
      intro k
      induction k with
      | zero =>
        have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
        simp only [Nat.cast_zero, mul_zero]; exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩
      | succ k ihk =>
        obtain ⟨c1, c2⟩ := pi_add h ihk.1 hwT.1
        rw [Nat.cast_succ, mul_add_one]; exact ⟨c1, by rw [c2, ihk.2, hwT.2]⟩
    obtain ⟨hrT, hrπ⟩ := IH r hrM (hrM.trans hME) hdr
    obtain ⟨c1, c2⟩ := pi_add h (hmul k).1 hrT
    rw [← hdec, hk]
    exact ⟨c1, by rw [c2, (hmul k).2, hrπ]⟩

/-- **`Ω₁·M ∈ Tᵗ[σ]` and `π_{σ,τ}(Ω₁·M) = Ω₁·M`** for `M < ε_{Ω₁+1}` with `rjDat M < σ` (`M < Ω₁`:
`Si.siOm1_mul_lt`; otherwise `Ω₁·M = Ω₁·ω^l·v + Ω₁·r`, `siOm1_opow_TB` with `uh_pi_fix` at `l`, induction at `r`). -/
theorem uh_Om1_mul_TB {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ M, M < Gg.ggE → Rj.rjDat M < σ → Om1 * M ∈ TB τ σ ∧ pi σ τ (Om1 * M) = Om1 * M := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hME hMd
  rcases lt_or_ge M Om1 with hM1 | hM1
  · rw [Rj.rjDat_small hM1] at hMd
    exact Si.siOm1_mul_lt h M hMd
  · have hM0 : M ≠ 0 := (lt_of_lt_of_le Rj.rj_Om1_pos hM1).ne'
    obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hM0
    set l := log ω M with hldef
    set v := M / ω ^ l with hvdef
    set r := M % ω ^ l with hrdef
    have hlE : l < Gg.ggE := (log_le_self ω M).trans_lt hME
    have hrM : r < M := hr.trans_le (opow_log_le_self ω hM0)
    have hdlr : Rj.rjDat l < σ ∧ Rj.rjDat r < σ := by
      rcases hM1.lt_or_eq with hM1 | hMe
      · have hM1' : Om1 < ω ^ l * v + r := by rw [hdec]; exact hM1
        have hME' : ω ^ l * v + r < Gg.ggE := by rw [hdec]; exact hME
        have hdat : Rj.rjDat M = max (Rj.rjDat l) (Rj.rjDat r) := by
          rw [← Si.si_rjDat_form hv0 hvω hr hM1' hME', hdec]
        exact ⟨(le_max_left _ _).trans_lt (hdat ▸ hMd), (le_max_right _ _).trans_lt (hdat ▸ hMd)⟩
      · have hl : l = Om1 := by
          rw [hldef, ← hMe]; conv_lhs => rw [← Rj.rj_Om1_opow]
          exact log_opow one_lt_omega0 _
        have hrr : r = 0 := by
          rw [hrdef, hl, ← hMe, Rj.rj_Om1_opow, Ordinal.mod_self]
        have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
        rw [hl, hrr, Rj.rjDat_Om1, Rj.rjDat_small Rj.rj_Om1_pos]; exact ⟨h0σ, h0σ⟩
    obtain ⟨hlT, hlπ⟩ := uh_pi_fix h l hlE hdlr.1
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hlE
    have hwT : Om1 * ω ^ l ∈ TB τ σ ∧ pi σ τ (Om1 * ω ^ l) = Om1 * ω ^ l :=
      ⟨o1.2 hlT, by rw [o2 hlT, hlπ]⟩
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
    have hmul : ∀ k : ℕ, Om1 * ω ^ l * (k : Ordinal.{0}) ∈ TB τ σ ∧
        pi σ τ (Om1 * ω ^ l * (k : Ordinal.{0})) = Om1 * ω ^ l * (k : Ordinal.{0}) := by
      intro k
      induction k with
      | zero =>
        have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
        simp only [Nat.cast_zero, mul_zero]; exact ⟨mem_TB_of_lt h h0σ, pi_lt h h0σ⟩
      | succ k ihk =>
        obtain ⟨c1, c2⟩ := pi_add h ihk.1 hwT.1
        rw [Nat.cast_succ, mul_add_one]; exact ⟨c1, by rw [c2, ihk.2, hwT.2]⟩
    obtain ⟨hrT, hrπ⟩ := IH r hrM (hrM.trans hME) hdlr.2
    obtain ⟨c1, c2⟩ := pi_add h (hmul k).1 hrT
    have e : Om1 * M = Om1 * ω ^ l * (k : Ordinal.{0}) + Om1 * r := by
      conv_lhs => rw [← hdec]
      rw [mul_add, ← mul_assoc, hk]
    rw [e]
    exact ⟨c1, by rw [c2, (hmul k).2, hrπ]⟩

/-- `Ω₁·M + x ∈ Tᵗ` and `< Ω₂` for a level `M` over `κ` (`κ < τ` a base) and `x ∈ Tᵗ ∩ Ω₁`. -/
theorem uh_arg_T {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : UhLev κ M) (hx : x ∈ Tset τ) (hx1 : x < Om1) :
    Om1 * M + x ∈ Tset τ ∧ Om1 * M + x < OmTwo :=
  ⟨vzT_add hB.2.1 hB.2.2.2 (uh_Om1_mul_TB hB M hM.2.1 hM.2.2).1.1 hx, Rj.rj_arg_lt hM.2.1 hx1⟩

/-- **The countable part is below the value**: `x < ϑᵗ(Ω₁·M + x)` for a level `M` over `κ < τ` and
`x ∈ Tᵗ ∩ Ω₁` ([W07a] Lemma 3.30: `luLt_vt_self` for `M < Ω₁`, `rjLevel_lt_vt` for `M ≥ Ω₁`). -/
theorem uhLt_vt_self {κ τ M x : Ordinal.{0}} (hB : Bases κ τ) (hM : UhLev κ M) (hx : x ∈ Tset τ)
    (hx1 : x < Om1) : x < vt τ (Om1 * M + x) := by
  rcases lt_or_ge M Om1 with hM1 | hM1
  · have hMκ : M < κ := by rw [← Rj.rjDat_small hM1]; exact hM.2.2
    exact luLt_vt_self hB.2.1 hB.2.2.2 hM.1 (hMκ.trans hB.2.2.1) hx hx1
  · exact (rjLevel_lt_vt hB.2.1 hB.2.2.2 hM1 hM.2.1
      (uh_T_le hB.2.1 hB.2.2.2 (hM.2.2.trans hB.2.2.1).le) hx hx1).2

/-- **Membership**: leaves in `Tᵗ`, the argument bounds and levels over `κ` give `t[τ] ∈ Tᵗ`. -/
theorem uhMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UhT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hq => vzT_add hB.2.1 hB.2.2.2 (uhMem hB s hl.1 hw.1 hq.1) (uhMem hB t hl.2 hw.2 hq.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hq => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (uhMem hB s hl hw.1 hq)) (Om1_add_lt hO hw.2)).1
  | .thc _ r, hl, hw, hq => by
    obtain ⟨h1, h2⟩ := uh_arg_T hB hq.1 (uhMem hB r hl hw.1 hq.2) hw.2
    exact (vt_memTwo hB.2.1 hB.2.2.2 h1 h2).1

/-- **Every leaf and every `thc`-value is `≤` the value** ([W07a] Lemma 3.30 through `luLt_vt_self`, Lemma 4.2
through `vt_wbar`). -/
theorem uhLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ t : UhT, Lv (· ∈ Tset τ) t → WF τ t → Qs κ t → Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t
  | .par _, _, _, _ => ⟨le_refl _, trivial⟩
  | .add s t, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := uhLe hB s hl.1 hw.1 hq.1
    obtain ⟨b1, b2⟩ := uhLe hB t hl.2 hw.2 hq.2
    have hs : ev τ s ≤ ev τ (.add s t) := le_self_add
    have ht : ev τ t ≤ ev τ (.add s t) := le_add_self
    exact ⟨⟨Lv_mono (fun p hp => hp.trans hs) s a1, Lv_mono (fun p hp => hp.trans ht) t b1⟩,
      ⟨Nd_mono (fun p hp => hp.trans hs) s a2, Nd_mono (fun p hp => hp.trans ht) t b2⟩⟩
  | .base, _, _, _ => ⟨trivial, trivial⟩
  | .th1 s, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := uhLe hB s hl hw.1 hq
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact ⟨Lv_mono (fun p hp => hp.trans hle) s a1, Nd_mono (fun p hp => hp.trans hle) s a2⟩
  | .thc q r, hl, hw, hq => by
    obtain ⟨a1, a2⟩ := uhLe hB r hl hw.1 hq.2
    have hrT := uhMem hB r hl hw.1 hq.2
    have hlt : ev τ r < ev τ (.thc q r) := uhLt_vt_self hB hq.1 hrT hw.2
    exact ⟨Lv_mono (fun p hp => hp.trans hlt.le) r a1, le_rfl, Nd_mono (fun p hp => hp.trans hlt.le) r a2⟩

/-! ## The base change on terms -/

/-- **The base change with a general parameter map** ([W07a] Def 5.1, Lemma 5.3 through `pi_lt`, `pi_base`,
`pi_add`, `pi_vt`, `pi_vt_two`, `uh_Om1_mul_TB`): for bases `σ < τ`, levels over `σ`, a term with the argument
bounds over `τ` whose leaves lie in `Tᵗ[σ]`: `t[τ] ∈ Tᵗ[σ]`, `π_{σ,τ}(t[τ; p]) = t[σ; π p]`, and the image has the
argument bounds over `σ`. -/
theorem uhDown {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UhT, WF τ t → Lv (· ∈ TB τ σ) t → Qs κ t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (t.map (pi σ τ)) ∧ WF σ (t.map (pi σ τ))
  | .par p, _, hp, _ => ⟨hp, rfl, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhDown h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := uhDown h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map]; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhDown h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhDown h hκσ r hw.1 hl hq.2
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ r < OmTwo := Rj.rj_arg_lt hq.1.2.1 hw.2
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (Om1 * q + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩⟩
    · simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2

/-- **The inverse base change on terms**: leaves in `T^σ` ⇒ the term over `τ` with leaves `π_{σ,τ}⁻¹ p` lies in
`Tᵗ[σ]`, has the argument bounds, and is sent by `π_{σ,τ}` to `t[σ; p]`. -/
theorem uhUp {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) :
    ∀ t : UhT, WF σ t → Lv (· ∈ Tset σ) t → Qs κ t →
      ev τ (t.map (up σ τ)) ∈ TB τ σ ∧ pi σ τ (ev τ (t.map (up σ τ))) = ev σ t ∧ WF τ (t.map (up σ τ))
  | .par p, _, hp, _ => ⟨(up_spec h hp).1, (up_spec h hp).2, trivial⟩
  | .add s t, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhUp h hκσ s hw.1 hl.1 hq.1
    obtain ⟨b1, b2, b3⟩ := uhUp h hκσ t hw.2 hl.2 hq.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩⟩
    simp only [ev, map] at c2 ⊢; rw [c2, a2, b2]
  | .base, _, _, _ => ⟨(pi_base h).1, (pi_base h).2, trivial⟩
  | .th1 s, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhUp h hκσ s hw.1 hl hq
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 : ev τ (s.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (s.map (up σ τ)) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | .thc q r, hw, hl, hq => by
    obtain ⟨a1, a2, a3⟩ := uhUp h hκσ r hw.1 hl hq.2
    have hy1 : ev τ (r.map (up σ τ)) < Om1 := by
      by_contra hge
      have hOm := pi_Om1 h
      have := ((pi_bijOn h).2.le_iff_le hOm.1 a1).2 (not_lt.1 hge)
      rw [hOm.2, a2] at this
      exact absurd hw.2 (not_lt.2 this)
    obtain ⟨g1, g2⟩ := uh_Om1_mul_TB h q hq.1.2.1 (hq.1.2.2.trans_le hκσ)
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 : Om1 * q + ev τ (r.map (up σ τ)) < OmTwo := Rj.rj_arg_lt hq.1.2.1 hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    refine ⟨⟨d1, by simp only [ev, map]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩⟩
    simp only [ev, map]; rw [pi_vt_two h c1 hlt2, c2, g2, a2]

/-- `π_{σ,τ}⁻¹(t[σ; p]) = t[τ; π⁻¹ p]`. -/
theorem uhUp_eq {κ σ τ : Ordinal.{0}} (h : Bases σ τ) (hκσ : κ ≤ σ) (t : UhT) (hw : WF σ t)
    (hl : Lv (· ∈ Tset σ) t) (hq : Qs κ t) :
    up σ τ (ev σ t) = ev τ (t.map (up σ τ)) ∧ WF τ (t.map (up σ τ)) := by
  obtain ⟨a1, a2, a3⟩ := uhUp h hκσ t hw hl hq
  exact ⟨by rw [← a2]; exact up_pi h a1, a3⟩

/-- **The segment move on terms**: for `ε`-numbers `b, c < Ω₁`, levels over `κ ≤ b, c` and leaves in `Tᵇ[κ]`:
`mv b c (t[b; p]) = t[c; mv b c p]`. -/
theorem uhMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UhT) (hq : Qs κ t) (hw : WF b t) (hl : Lv (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (t.map (mv b c)) ∧ WF c (t.map (mv b c)) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3⟩ := uhDown hB hκc t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hq
    rw [hmv]; exact ⟨a2, a3⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, map_id]; exact ⟨rfl, hw⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact uhUp_eq hB hκb t hw (Lv_mono (fun p hp => hp.1) t hl) hq

/-! ## The translations of [W07a] Def 6.2 -/

/-- **`t^α_τ` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.uhVt_tr` (i) and `R2.vt_wbar`): for
`α = Dl τ n` (`n ≥ 1`), levels over `κ < τ`, leaves in `T^α`, the argument bounds over `α`, and every `thc`-value
over `α` below `α⁺ = Dp τ n`: `tr α t` has the argument bounds over `τ` and `(tr α t)[τ] = t[α]`. -/
theorem uhTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UhT, Qs κ t → Lv (· ∈ Tset (Dl τ n)) t → WF (Dl τ n) t → Nd (Dl τ n) (· < Dp τ n) t →
      WF τ (tr (Dl τ n) t) ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrA hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2⟩ := uhTrA hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrA hB hn s hq hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrA hB hn r hq.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2
    have hrT := uhMem hBα r hl hw.1 hq.2
    have hargT := (uh_arg_T hBα hq.1 hrT hw.2).1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hw.2).1 hargT hd.1
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ?_⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [tr, ev]; rw [a2, e]

/-- **`t^τ_α` is correct** ([W07a] Def 6.2, Lemma 6.3 through `R2.uhVt_tr` (ii) and `R2.vt_wbar`): for
`α = Dl τ n` (`n ≥ 1`), levels over `κ < τ`, if `tr α t` has the argument bounds over `τ`, leaves in `Tᵗ`, and every
`thc`-value of `tr α t` over `τ` is below `α⁺ = Dp τ n`, then `t` has the argument bounds over `α` and
`(tr α t)[τ] = t[α]`. -/
theorem uhTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : UhT, Qs κ t → Lv (· ∈ Tset τ) (tr (Dl τ n) t) → WF τ (tr (Dl τ n) t) →
      Nd τ (· < Dp τ n) (tr (Dl τ n) t) → WF (Dl τ n) t ∧ ev τ (tr (Dl τ n) t) = ev (Dl τ n) t
  | .par _, _, _, _, _ => ⟨trivial, rfl⟩
  | .add s t, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrB hB hn s hq.1 hl.1 hw.1 hd.1
    obtain ⟨b1, b2⟩ := uhTrB hB hn t hq.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, b2]
  | .base, _, _, _, _ => ⟨trivial, rfl⟩
  | .th1 s, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrB hB hn s hq hl.2 hw.1.2 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, ?_⟩
    simp only [tr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | .thc q r, hq, hl, hw, hd => by
    obtain ⟨a1, a2⟩ := uhTrB hB hn r hq.2 hl.2 hw.1.2 hd.2.2
    have h2 := hw.2
    simp only [ev] at h2
    have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact lt_of_le_of_lt le_add_self h2
    -- the argument over `τ` is in `Tᵗ`
    have hαT : Dl τ n ∈ Tset τ := (Dl_spec hB.2.1 hB.2.2.2 n).1
    have hrT : ev τ (tr (Dl τ n) r) ∈ Tset τ :=
      uhMem hB _ hl.2 hw.1.2 (Qs_tr _ r hq.2)
    have hsT : Dl τ n + ev τ (tr (Dl τ n) r) ∈ Tset τ := vzT_add hB.2.1 hB.2.2.2 hαT hrT
    have hargT := (uh_arg_T hB hq.1 hsT h2).1
    have hd1 := hd.1
    simp only [ev] at hd1
    rw [a2] at hargT hd1
    have e := (uhVt_tr hB.2.1 hB.2.2.2 hn hq.1.1 hq.1.2.1 (hq.1.2.2.trans hB.2.2.1) hr1).2 hargT hd1
    refine ⟨⟨a1, hr1⟩, ?_⟩
    simp only [tr, ev]; rw [a2, e]

/-! ## The countable-argument terms of `Ub.UbT` -/

/-- The countable-argument terms of `Ub.UbT` as terms of `UhT` (`th`, `om` nodes are not used: sent to `base`). -/
def ofUb : Ub.UbT → UhT
  | .par p => .par p
  | .add s t => .add (ofUb s) (ofUb t)
  | .base => .base
  | .th1 s => .th1 (ofUb s)
  | .th _ => .base
  | .om _ => .base

theorem ofUb_ev (τ : Ordinal.{0}) : ∀ t : Ub.UbT, Ub.UbT.IsA t → ev τ (ofUb t) = Ub.UbT.ev τ t
  | .par _, _ => rfl
  | .add s t, h => by simp only [ofUb, ev, Ub.UbT.ev, ofUb_ev τ s h.1, ofUb_ev τ t h.2]
  | .base, _ => rfl
  | .th1 s, h => by simp only [ofUb, ev, Ub.UbT.ev, ofUb_ev τ s h]
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : Ub.UbT, ofUb (t.map f) = (ofUb t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUb, map, Ub.UbT.map, ofUb_map f s, ofUb_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUb, map, Ub.UbT.map, ofUb_map f s]
  | .th _ => rfl
  | .om _ => rfl

theorem ofUb_WF (τ : Ordinal.{0}) : ∀ t : Ub.UbT, Ub.UbT.IsA t → (WF τ (ofUb t) ↔ Ub.UbT.WF τ t)
  | .par _, _ => Iff.rfl
  | .add s t, h => by
    simp only [ofUb, WF, Ub.UbT.WF]; rw [ofUb_WF τ s h.1, ofUb_WF τ t h.2]
  | .base, _ => Iff.rfl
  | .th1 s, h => by
    simp only [ofUb, WF, Ub.UbT.WF]; rw [ofUb_WF τ s h, ofUb_ev τ s h]
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_Lv {P : Ordinal.{0} → Prop} : ∀ t : Ub.UbT, Ub.UbT.IsA t → (Lv P (ofUb t) ↔ Ub.UbT.Lv P t)
  | .par _, _ => Iff.rfl
  | .add s t, h => by
    simp only [ofUb, Lv, Ub.UbT.Lv]; rw [ofUb_Lv s h.1, ofUb_Lv t h.2]
  | .base, _ => Iff.rfl
  | .th1 s, h => by simp only [ofUb, Lv, Ub.UbT.Lv]; exact ofUb_Lv s h
  | .th _, h => h.elim
  | .om _, h => h.elim

theorem ofUb_Qs (κ : Ordinal.{0}) : ∀ t : Ub.UbT, Qs κ (ofUb t)
  | .par _ => trivial
  | .add s t => ⟨ofUb_Qs κ s, ofUb_Qs κ t⟩
  | .base => trivial
  | .th1 s => ofUb_Qs κ s
  | .th _ => trivial
  | .om _ => trivial

/-- The data `rjDat M` of the levels `M` of the `thc`-nodes. -/
noncomputable def lvq : UhT → Finset Ordinal.{0}
  | .par _ => ∅
  | .add s t => lvq s ∪ lvq t
  | .base => ∅
  | .th1 s => lvq s
  | .thc q r => insert (Rj.rjDat q) (lvq r)

/-- Levels over `b` whose data are below `γ` are levels over `γ`. -/
theorem Qs_of_lvq {b γ : Ordinal.{0}} : ∀ t : UhT, Qs b t → (∀ q ∈ lvq t, q < γ) → Qs γ t
  | .par _, _, _ => trivial
  | .add s t, h, hq => ⟨Qs_of_lvq s h.1 (fun q hq' => hq q (Finset.mem_union_left _ hq')),
      Qs_of_lvq t h.2 (fun q hq' => hq q (Finset.mem_union_right _ hq'))⟩
  | .base, _, _ => trivial
  | .th1 s, h, hq => Qs_of_lvq s h hq
  | .thc _ r, h, hq => ⟨⟨h.1.1, h.1.2.1, hq _ (Finset.mem_insert_self _ _)⟩,
      Qs_of_lvq r h.2 (fun q' hq' => hq q' (Finset.mem_insert_of_mem hq'))⟩

/-- The data of the levels of a term with levels over `b` are below `b`. -/
theorem lvq_lt {b : Ordinal.{0}} : ∀ t : UhT, Qs b t → ∀ q ∈ lvq t, q < b
  | .par _, _, q, hq => absurd hq (Finset.notMem_empty q)
  | .add s t, h, q, hq => by
    rcases Finset.mem_union.1 hq with hq | hq
    · exact lvq_lt s h.1 q hq
    · exact lvq_lt t h.2 q hq
  | .base, _, q, hq => absurd hq (Finset.notMem_empty q)
  | .th1 s, h, q, hq => lvq_lt s h q hq
  | .thc q' r, h, q, hq => by
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h.1.2.2
    · exact lvq_lt r h.2 q hq

/-- The set of leaves. -/
noncomputable def lvs : UhT → Finset Ordinal.{0}
  | .par p => {p}
  | .add s t => lvs s ∪ lvs t
  | .base => ∅
  | .th1 s => lvs s
  | .thc _ r => lvs r

theorem Lv_lvs : ∀ t : UhT, Lv (· ∈ lvs t) t
  | .par _ => Finset.mem_singleton_self _
  | .add s t => ⟨Lv_mono (fun _ hp => Finset.mem_union_left _ hp) s (Lv_lvs s),
      Lv_mono (fun _ hp => Finset.mem_union_right _ hp) t (Lv_lvs t)⟩
  | .base => trivial
  | .th1 s => Lv_lvs s
  | .thc _ r => Lv_lvs r

theorem mem_lvs {P : Ordinal.{0} → Prop} : ∀ {t : UhT}, Lv P t → ∀ p ∈ lvs t, P p
  | .par _, h, p, hp => by rw [lvs, Finset.mem_singleton] at hp; rw [hp]; exact h
  | .add s t, h, p, hp => by
    rcases Finset.mem_union.1 hp with hp | hp
    · exact mem_lvs (t := s) h.1 p hp
    · exact mem_lvs (t := t) h.2 p hp
  | .base, _, p, hp => absurd hp (Finset.notMem_empty p)
  | .th1 s, h, p, hp => mem_lvs (t := s) h p hp
  | .thc _ r, h, p, hp => mem_lvs (t := r) h p hp

/-! ## The terms of `Ue.UeT` and the old citation -/

/-- The terms of `Ue.UeT` (constant levels `q < κ`) as terms of `UhT`. -/
def ofUe : Ue.UeT → UhT
  | .par p => .par p
  | .add s t => .add (ofUe s) (ofUe t)
  | .base => .base
  | .th1 s => .th1 (ofUe s)
  | .thc q r => .thc q (ofUe r)

theorem ofUe_ev (τ : Ordinal.{0}) : ∀ t : Ue.UeT, ev τ (ofUe t) = Ue.UeT.ev τ t
  | .par _ => rfl
  | .add s t => by simp only [ofUe, ev, Ue.UeT.ev, ofUe_ev τ s, ofUe_ev τ t]
  | .base => rfl
  | .th1 s => by simp only [ofUe, ev, Ue.UeT.ev, ofUe_ev τ s]
  | .thc _ r => by simp only [ofUe, ev, Ue.UeT.ev, ofUe_ev τ r]

theorem ofUe_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ t : Ue.UeT, ofUe (t.map f) = (ofUe t).map f
  | .par _ => rfl
  | .add s t => by simp only [ofUe, map, Ue.UeT.map, ofUe_map f s, ofUe_map f t]
  | .base => rfl
  | .th1 s => by simp only [ofUe, map, Ue.UeT.map, ofUe_map f s]
  | .thc _ r => by simp only [ofUe, map, Ue.UeT.map, ofUe_map f r]

theorem ofUe_WF (τ : Ordinal.{0}) : ∀ t : Ue.UeT, WF τ (ofUe t) ↔ Ue.UeT.WF τ t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUe, WF, Ue.UeT.WF]; rw [ofUe_WF τ s, ofUe_WF τ t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUe, WF, Ue.UeT.WF]; rw [ofUe_WF τ s, ofUe_ev τ s]
  | .thc _ r => by simp only [ofUe, WF, Ue.UeT.WF]; rw [ofUe_WF τ r, ofUe_ev τ r]

theorem ofUe_Lv {P : Ordinal.{0} → Prop} : ∀ t : Ue.UeT, Lv P (ofUe t) ↔ Ue.UeT.Lv P t
  | .par _ => Iff.rfl
  | .add s t => by simp only [ofUe, Lv, Ue.UeT.Lv]; rw [ofUe_Lv s, ofUe_Lv t]
  | .base => Iff.rfl
  | .th1 s => by simp only [ofUe, Lv, Ue.UeT.Lv]; exact ofUe_Lv s
  | .thc _ r => by simp only [ofUe, Lv, Ue.UeT.Lv]; exact ofUe_Lv r

/-- A constant level `1 ≤ q < κ ≤ Ω₁` is a level over `κ` (`rjDat q = q`). -/
theorem ofUe_Qs {κ : Ordinal.{0}} (hκ : κ ≤ Om1) : ∀ t : Ue.UeT, Ue.UeT.Qs κ t → Qs κ (ofUe t)
  | .par _, _ => trivial
  | .add s t, h => ⟨ofUe_Qs hκ s h.1, ofUe_Qs hκ t h.2⟩
  | .base, _ => trivial
  | .th1 s, h => ofUe_Qs hκ s h
  | .thc q r, h => by
    have hq1 : q < Om1 := h.2.1.trans_le hκ
    exact ⟨⟨h.1, hq1.trans Rj.rj_Om1_lt_E, by rw [Rj.rjDat_small hq1]; exact h.2.1⟩, ofUe_Qs hκ r h.2.2⟩

/-- **`R2.ueVt_tr` is the case `M = q < Ω₁` of `R2.uhVt_tr`** (`rjDat q = q`). -/
theorem uhVt_tr_ue {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {q ρ : Ordinal.{0}}
    (hq1 : 1 ≤ q) (hqτ : q < τ) (hρ1 : ρ < Om1) :
    (Om1 * q + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * q + ρ) < Dp τ n →
      vt (Dl τ n) (Om1 * q + ρ) = vt τ (Om1 * q + (Dl τ n + ρ))) ∧
    (Om1 * q + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * q + (Dl τ n + ρ)) < Dp τ n →
      vt τ (Om1 * q + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * q + ρ)) := by
  have hqO : q < Om1 := hqτ.trans hτ1
  exact uhVt_tr hτ hτ1 hn hq1 (hqO.trans Rj.rj_Om1_lt_E) (by rw [Rj.rjDat_small hqO]; exact hqτ) hρ1

end Googology.Trans.PoR.InaccPsi.R2.Uh
