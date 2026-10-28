import Googology.Trans.PoR.InaccPsi.R2.ViTerm

/-!
# The translations of [W07a] Def 6.2 on terms with the node `thz G r` at every level `G = Ω₁·M < B₂`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`α = Dl τ n = ϑᵗ(Δₙ)`, `α⁺ = Dp τ n`.  The translation `vtr a` is `Ur.trr a` except at a node `thz (Ω₁·q) r`
(`thc q r`), where it is **decided by the leaves of the level**: every leaf of `Ω₁·q` below `a` ⇒
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + a + ρ)` (the subcase `Γ^* < α`, `Vc.vc_node_trL` from `R2.uvVt_trL`); some leaf `≥ a` ⇒
`ϑ^a(Ω₁·q + ρ) ↦ ϑ^b(Ω₁·q + ρ)` (the subcase `Γ^* ≥ α`, `Vc.vc_node_trH` from `R2.uvVt_trH`).  The level `Ω₁·q` is
an ordinal, kept by both translations (as in the cited statements).

* `vi_gm`, `vi_nz`, `vi_nz_of_lv` (the node conditions `Vi.Nz` from membership of the argument, `Si.siT_of_comps`,
  `Vi.vi_comps_head`);
* `viTrAB`, `viTrA` (**`t^α_τ` is correct**: `vtr α t` has the argument bounds and node conditions over `τ` and the
  same value), `viTrBB`, `viTrB` (**`t^τ_α` is correct**).

New definition: `vtr`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vi

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vc

open Classical in
/-- **The translation `t^a_b` of [W07a] Def 6.2 with ordinal levels decided by their leaves.** -/
noncomputable def vtr (a : Ordinal.{0}) : {k : Bool} → UnT k → UnT k
  | _, .par p => .par p
  | _, .add s t => .add (vtr a s) (vtr a t)
  | _, .base => .par a
  | _, .th1 s => .th1 (.add (.par a) (vtr a s))
  | _, .thc q r => if VcLv (· < a) (Om1 * q) then .thc q (.add (.par a) (vtr a r)) else .thc q (vtr a r)
  | _, .thg m G r => if LoL a G then .thg m (vtr a G) (.add (.par a) (vtr a r)) else .thg m (vtr a G) (vtr a r)
  | _, .lf c => .lf (vtr a c)
  | _, .om b => .om (vtr a b)
  | _, .ad x y => .ad (vtr a x) (vtr a y)

theorem vtr_thc_lo {a q : Ordinal.{0}} {r : UnT false} (h : VcLv (· < a) (Om1 * q)) :
    vtr a (.thc q r) = .thc q (.add (.par a) (vtr a r)) := by
  simp only [vtr, if_pos h]

theorem vtr_thc_hi {a q : Ordinal.{0}} {r : UnT false} (h : ¬ VcLv (· < a) (Om1 * q)) :
    vtr a (.thc q r) = .thc q (vtr a r) := by
  simp only [vtr, if_neg h]

theorem vtr_thg_lo {a : Ordinal.{0}} {m : Bool} {G : UnT true} {r : UnT false} (h : LoL a G) :
    vtr a (.thg m G r) = .thg m (vtr a G) (.add (.par a) (vtr a r)) := by
  simp only [vtr, if_pos h]

theorem vtr_thg_hi {a : Ordinal.{0}} {m : Bool} {G : UnT true} {r : UnT false} (h : ¬ LoL a G) :
    vtr a (.thg m G r) = .thg m (vtr a G) (vtr a r) := by
  simp only [vtr, if_neg h]

/-- **A low level is not translated.** -/
theorem vtr_LoL {a b : Ordinal.{0}} : ∀ {k : Bool} (G : UnT k), LoL b G → vtr a G = G
  | _, .lf (.par _), _ => rfl
  | _, .om b', h => by simp only [vtr, vtr_LoL b' h]
  | _, .ad x y, h => by simp only [vtr, vtr_LoL x h.1, vtr_LoL y h.2]
  | _, .lf (.add _ _), h => h.elim
  | _, .lf .base, h => h.elim
  | _, .lf (.th1 _), h => h.elim
  | _, .lf (.thc _ _), h => h.elim
  | _, .lf (.thg _ _ _), h => h.elim
  | _, .par _, h => h.elim
  | _, .add _ _, h => h.elim
  | _, .base, h => h.elim
  | _, .th1 _, h => h.elim
  | _, .thc _ _, h => h.elim
  | _, .thg _ _ _, h => h.elim

theorem Gs_vtr (a : Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Gs (vtr a t) ↔ Gs t
  | _, .par _ => Iff.rfl
  | _, .add _ _ => Iff.rfl
  | _, .base => Iff.rfl
  | _, .th1 _ => Iff.rfl
  | _, .thc q _ => by
    by_cases h : VcLv (· < a) (Om1 * q)
    · rw [vtr_thc_lo h]; exact Iff.rfl
    · rw [vtr_thc_hi h]; exact Iff.rfl
  | _, .thg _ G _ => by
    by_cases h : LoL a G
    · rw [vtr_thg_lo h]; exact Iff.rfl
    · rw [vtr_thg_hi h]; exact Iff.rfl
  | _, .lf _ => Iff.rfl
  | _, .om _ => Iff.rfl
  | _, .ad x y => and_congr (Gs_vtr a x) (Gs_vtr a y)

theorem IsOm_vtr (a : Ordinal.{0}) : ∀ (t : UnT true), IsOm (vtr a t) ↔ IsOm t
  | .lf _ => Iff.rfl
  | .om _ => Iff.rfl
  | .ad _ _ => Iff.rfl

theorem HiC_vtr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (c : UnT false), HiC a c → HiC τ (vtr a c)
  | .par _, h => hτa.trans h
  | .add s _, h => HiC_vtr hτa s h
  | .base, _ => hτa
  | .th1 _, _ => trivial
  | .thc q _, _ => by
    by_cases h : VcLv (· < a) (Om1 * q)
    · rw [vtr_thc_lo h]; trivial
    · rw [vtr_thc_hi h]; trivial
  | .thg _ G _, _ => by
    by_cases h : LoL a G
    · rw [vtr_thg_lo h]; trivial
    · rw [vtr_thg_hi h]; trivial

theorem Hd_vtr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), Hd a G → Hd τ (vtr a G)
  | .lf c, h => HiC_vtr hτa c h
  | .om b, h => Hd_vtr hτa b h
  | .ad x _, h => Hd_vtr hτa x h

theorem HdE_vtr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (G : UnT true), HdE a G → HdE τ (vtr a G)
  | .lf c, h => HiC_vtr hτa c h
  | .om b, h => HdE_vtr hτa b h
  | .ad x y, h => h.imp (HdE_vtr hτa x) (HdE_vtr hτa y)

theorem HdM_vtr {τ a : Ordinal.{0}} (hτa : τ ≤ a) : ∀ (m : Bool) (G : UnT true), HdM m a G → HdM m τ (vtr a G)
  | false, G, h => Hd_vtr hτa G h
  | true, G, h => HdE_vtr hτa G h

/-! ## The node conditions from membership -/

/-- `Ω₁·q ∈ Tᵗ` from `Ω₁·q + ρ ∈ Tᵗ` (`ρ < Ω₁`, `q ≥ 1`): the components of `Ω₁·q` are components of the sum. -/
theorem vi_gm {τ q ρ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hq1 : 1 ≤ q) (hm : Om1 * q + ρ ∈ Tset τ)
    (hρ : ρ < Om1) : Om1 * q ∈ Tset τ := by
  have hle : Om1 ≤ Om1 * q := by
    have := mul_le_mul_right hq1 Om1
    rwa [mul_one] at this
  have hτx : τ ≤ Om1 * q + ρ := (hτ1.le.trans hle).trans le_self_add
  have hOm : (ω : Ordinal.{0}) ^ (Om1 : Ordinal.{0}) = Om1 := Rj.rj_Om1_opow
  have hda : ω ^ (Om1 : Ordinal.{0}) ∣ Om1 * q := by rw [hOm]; exact dvd_mul_right _ _
  have hρw : ρ < ω ^ (Om1 : Ordinal.{0}) := by rw [hOm]; exact hρ
  exact Si.siT_of_comps hτ hτ1 _ fun p hp =>
    (Par_comps_eq hτ hτ1 hm hτx).1 p (vi_comps_head _ hda ρ hρw p hp)

theorem vi_nz {τ q ρ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hq1 : 1 ≤ q) (hqB : Om1 * q < Uc.ucB)
    (hm : Om1 * q + ρ ∈ Tset τ) (hρ : ρ < Om1) (hrb : ρ < vt τ (Om1 * q + ρ)) : Nz τ q ρ :=
  ⟨hq1, hqB, vi_gm hτ hτ1 hq1 hm hρ, hm, hrb⟩

/-- **The node conditions are satisfiable at every level `Ω₁·q` with `Ω₁ ≤ q < B₂` whose leaves lie in `Tᵗ`**
(`Vc.vc_arg_mem`, `Vc.vc_level_lt`, i.e. `R2.ucArg_mem`, `R2.ucLevel_lt`), for every `ρ ∈ Tᵗ ∩ Ω₁`. -/
theorem vi_nz_of_lv {τ q ρ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hq : Om1 ≤ q) (hqB : q < Uc.ucB)
    (hL : VcLv (· ∈ Tset τ) q) (hρ : ρ ∈ Tset τ) (hρ1 : ρ < Om1) : Nz τ q ρ :=
  vi_nz hτ hτ1 (Order.one_le_iff_pos.2 (Rj.rj_Om1_pos.trans_le hq)) (vc_arg_lt hqB hρ1).1
    (vc_arg_mem hτ hτ1 hq hqB hL hρ hρ1) hρ1 (vc_level_lt hτ hτ1 hq hqB hL hρ hρ1).2.1

/-! ## The translations -/

/-- **`t^α_τ` on terms of both sorts.** -/
theorem viTrAB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), ZW (Dl τ n) t → Lv (· ∈ Tset (Dl τ n)) t → WFr (Dl τ n) t →
      Nd (Dl τ n) (· < Dp τ n) t →
      WFr τ (vtr (Dl τ n) t) ∧ ZW τ (vtr (Dl τ n) t) ∧ ev τ (vtr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS (Dl τ n) t → HbS τ (vtr (Dl τ n) t)) ∧ (FNF (Dl τ n) t → FNF τ (vtr (Dl τ n) t)) ∧
      (∀ V, Lf (fun c => ev τ c < V) (vtr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _ => ⟨trivial, trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, -⟩ := viTrAB hB hn s hz.1 hl.1 hw.1 hd.1
    obtain ⟨b1, bz, b2, -⟩ := viTrAB hB hn t hz.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ⟨az, bz⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [vtr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _ => ⟨trivial, trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, -⟩ := viTrAB hB hn s hz hl hw.1 hd
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have hlt : Dl τ n + ev (Dl τ n) s < Om1 := Om1_add_lt hα1 hw.2
    refine ⟨⟨⟨trivial, a1⟩, ?_⟩, ⟨trivial, az⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    · simp only [ev]; rw [a2]; exact hlt
    · simp only [vtr, ev]
      rw [a2, vt_wbar hB.2.1 hB.2.2.2 hlt, vt_wbar hαE hα1 hw.2, ← add_assoc, hab]
  | _, .thc q r, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, -⟩ := viTrAB hB hn r hz.2 hl hw.1 hd.2
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hρ1 : ev (Dl τ n) r < Om1 := hw.2
    have hd1 : vt (Dl τ n) (Om1 * q + ev (Dl τ n) r) < Dp τ n := hd.1
    by_cases hL : VcLv (· < Dl τ n) (Om1 * q)
    · -- every leaf below `α`: `α` is inserted (`Vc.vc_node_trL` (i))
      rw [vtr_thc_lo hL]
      obtain ⟨m1, e1⟩ := (vc_node_trL hB.2.1 hB.2.2.2 hn hz.1.q1 hz.1.qB hρ1 hL).1 hz.1.mem hd1
      have hlt : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hρ1
      have hev : ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r)) = Dl τ n + ev (Dl τ n) r := by
        simp only [ev]; rw [a2]
      have hle : Om1 ≤ Om1 * q := by
        have := mul_le_mul_right hz.1.q1 Om1
        rwa [mul_one] at this
      obtain ⟨hαV, hVE⟩ := (vt_E_iff hαE hα1 hz.1.mem (nz_arg_lt hz.1 hρ1)).2 (hle.trans le_self_add)
      have hrb : Dl τ n + ev (Dl τ n) r < vt (Dl τ n) (Om1 * q + ev (Dl τ n) r) := hVE.add_lt hαV hz.1.rb
      refine ⟨⟨⟨trivial, a1⟩, by rw [hev]; exact hlt⟩,
        ⟨by rw [hev]; exact vi_nz hB.2.1 hB.2.2.2 hz.1.q1 hz.1.qB m1 hlt (by rw [← e1]; exact hrb), trivial, az⟩,
        ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      show vt τ (Om1 * q + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r))) = vt (Dl τ n) (Om1 * q + ev (Dl τ n) r)
      rw [hev, e1]
    · -- some leaf `≥ α`: the argument is kept (`Vc.vc_node_trH` (i))
      rw [vtr_thc_hi hL]
      obtain ⟨m1, e1⟩ := (vc_node_trH hB.2.1 hB.2.2.2 hn hz.1.q1 hz.1.qB hρ1 hL).1 hz.1.mem hd1
      refine ⟨⟨a1, by rw [a2]; exact hρ1⟩,
        ⟨by rw [a2]; exact vi_nz hB.2.1 hB.2.2.2 hz.1.q1 hz.1.qB m1 hρ1 (by rw [← e1]; exact hz.1.rb), az⟩,
        ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      show vt τ (Om1 * q + ev τ (vtr (Dl τ n) r)) = vt (Dl τ n) (Om1 * q + ev (Dl τ n) r)
      rw [a2, e1]
  | _, .thg m G r, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, -⟩ := viTrAB hB hn r hz.2 hl.2 hw.2.1 hd.2.2
    obtain ⟨l1, lz, l2, l4, l5, l6⟩ := viTrAB hB hn G hz.1 hl.1 hw.1 hd.2.1
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hw.2.2.gs
    have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G hw.1
    have hmem := hw.2.2.mem
    have hlt : vt (Dl τ n) (ev (Dl τ n) G + ev (Dl τ n) r) < Dp τ n := hd.1
    rw [hM] at hmem hlt
    by_cases hLo : LoL (Dl τ n) G
    · have hm : m = true := HdD_lo hw.2.2.hd hLo
      subst hm
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G hw.1 hw.2.2.nf hLo
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [vtr_thg_lo hLo]
      have hev : ev τ (vtr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hρα : Dl τ n + ev (Dl τ n) r < Om1 := Om1_add_lt hα1 hw.2.2.r1
      have h1M : Om1 ≤ Om1 * M := by
        have := mul_le_mul_right hM1 Om1
        rwa [mul_one] at this
      have hlt2 : Om1 * M + ev (Dl τ n) r < OmTwo := Uk.arg_lt2 hME hw.2.2.r1
      obtain ⟨hαV, hVE⟩ := (vt_E_iff hαE hα1 hmem hlt2).2 (h1M.trans le_self_add)
      have hrb0 : ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := by
        have := hw.2.2.rb; rw [hM] at this; exact this
      have hrb : Dl τ n + ev (Dl τ n) r < vt (Dl τ n) (Om1 * M + ev (Dl τ n) r) := hVE.add_lt hαV hrb0
      refine ⟨⟨l1, ⟨trivial, a1⟩, ⟨?_, (Gs_vtr _ G).2 hw.2.2.gs, l5 hw.2.2.nf, ?_, by rw [hev]; exact m1, ?_,
        ?_⟩⟩, ⟨lz, trivial, az⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      · show Dl τ n + ev τ (vtr (Dl τ n) r) < Om1
        rw [a2]; exact hρα
      · rw [vtr_LoL G hLo]
        rcases LoL_split (τ := τ) G hLo with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨rfl, h'⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1]
        show Dl τ n + ev τ (vtr (Dl τ n) r) < _
        rw [a2]; exact hrb
      · simp only [ev]; rw [l2, a2, hM]; exact e1.symm
    · have hHd : HdM m (Dl τ n) G := HdD_hi hw.2.2.hd hLo
      have hdat := (viDatM hBα m G hl.1 hw.1 hz.1 hw.2.2.nf hHd).1
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hw.2.2.r1).1 hmem hlt
      rw [vtr_thg_hi hLo]
      have hev : ev τ (vtr (Dl τ n) G) + ev τ (vtr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      refine ⟨⟨l1, a1, ⟨by rw [a2]; exact hw.2.2.r1, (Gs_vtr _ G).2 hw.2.2.gs, NfM_imp l4 l5 m hw.2.2.nf,
        Or.inl (HdM_vtr hτα.le m G hHd), by rw [hev]; exact m1, ?_, ?_⟩⟩, ⟨lz, az⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hev, ← e1, l6, ← hM]; exact hw.2.2.bd
      · rw [hev, ← e1, a2, ← hM]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, ← e1, hM]
  | _, .lf c, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, -⟩ := viTrAB hB hn c hz hl hw.1 hd
    refine ⟨⟨a1, by rw [a2]; exact hw.2⟩, az, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (vtr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, a4, a5, a6⟩ := viTrAB hB hn b hz hl hw hd
    refine ⟨a1, az, ?_, a4, a5, a6⟩
    simp only [vtr, ev]; rw [a2]
  | _, .ad x y, hz, hl, hw, hd => by
    obtain ⟨a1, az, a2, a4, a5, a6⟩ := viTrAB hB hn x hz.1 hl.1 hw.1 hd.1
    obtain ⟨b1, bz, b2, b4, b5, b6⟩ := viTrAB hB hn y hz.2 hl.2 hw.2 hd.2
    refine ⟨⟨a1, b1⟩, ⟨az, bz⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_vtr _ x).2 hb.2.1, by rw [a2, b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_vtr _ x).2 hb.2.2.1, by rw [a2, b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [vtr, ev]; rw [a2, b2]

/-- **`t^α_τ` is correct** (`α = Dl τ n`, `n ≥ 1`): `vtr α t` has the argument bounds and node conditions over `τ`
and `(vtr α t)[τ] = t[α]`; at a node `thz G r` the level `G = Ω₁·q < B₂` may have any leaves. -/
theorem viTrA {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false) (hz : ZW (Dl τ n) t)
    (hl : Lv (· ∈ Tset (Dl τ n)) t) (hw : WFr (Dl τ n) t) (hd : Nd (Dl τ n) (· < Dp τ n) t) :
    WFr τ (vtr (Dl τ n) t) ∧ ZW τ (vtr (Dl τ n) t) ∧ ev τ (vtr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, a3, -⟩ := viTrAB hB hn t hz hl hw hd
  exact ⟨a1, a2, a3⟩

/-- **`t^τ_α` on terms of both sorts.** -/
theorem viTrBB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ {k : Bool} (t : UnT k), Lv (· ∈ Tset τ) (vtr (Dl τ n) t) → WFr τ (vtr (Dl τ n) t) →
      ZW τ (vtr (Dl τ n) t) → Nd τ (· < Dp τ n) (vtr (Dl τ n) t) → HdDA (Dl τ n) t →
      Lv (· ∈ Tset (Dl τ n)) t →
      WFr (Dl τ n) t ∧ ZW (Dl τ n) t ∧ ev τ (vtr (Dl τ n) t) = ev (Dl τ n) t ∧
      (HbS τ (vtr (Dl τ n) t) → HbS (Dl τ n) t) ∧ (FNF τ (vtr (Dl τ n) t) → FNF (Dl τ n) t) ∧
      (∀ V, Lf (fun c => ev τ c < V) (vtr (Dl τ n) t) ↔ Lf (fun c => ev (Dl τ n) c < V) t)
  | _, .par _, _, _, _, _, _, _ => ⟨trivial, trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .add s t, hl, hw, hz, hd, hh, hla => by
    obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn s hl.1 hw.1 hz.1 hd.1 hh.1 hla.1
    obtain ⟨b1, bz, b2, -⟩ := viTrBB hB hn t hl.2 hw.2 hz.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ⟨az, bz⟩, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [vtr, ev]; rw [a2, b2]
  | _, .base, _, _, _, _, _, _ => ⟨trivial, trivial, rfl, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
  | _, .th1 s, hl, hw, hz, hd, hh, hla => by
    obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn s hl.2 hw.1.2 hz.2 hd.2 hh hla
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hab : τ + Dl τ n = Dl τ n :=
      add_of_omega0_opow_le (show τ < ω ^ Dl τ n by rw [hαE]; exact hτα) (le_of_eq hαE)
    have h2 := hw.2
    simp only [ev] at h2; rw [a2] at h2
    have hs1 : ev (Dl τ n) s < Om1 := lt_of_le_of_lt le_add_self h2
    refine ⟨⟨a1, hs1⟩, az, ?_, fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
    simp only [vtr, ev]
    rw [a2, vt_wbar hB.2.1 hB.2.2.2 h2, vt_wbar hαE hα1 hs1, ← add_assoc, hab]
  | _, .thc q r, hl, hw, hz, hd, hh, hla => by
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    by_cases hL : VcLv (· < Dl τ n) (Om1 * q)
    · -- every leaf below `α`: `Vc.vc_node_trL` (ii)
      rw [vtr_thc_lo hL] at hl hw hz hd ⊢
      obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn r hl.2 hw.1.2 hz.2.2 hd.2.2 hh hla
      have h2 : Dl τ n + ev (Dl τ n) r < Om1 := by
        have := hw.2; simp only [ev] at this; rwa [a2] at this
      have hr1 : ev (Dl τ n) r < Om1 := lt_of_le_of_lt le_add_self h2
      have hev : ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r)) = Dl τ n + ev (Dl τ n) r := by
        simp only [ev]; rw [a2]
      have hm := hz.1.mem
      have hrb := hz.1.rb
      have hd1 : vt τ (Om1 * q + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r))) < Dp τ n := hd.1
      rw [hev] at hm hrb hd1
      obtain ⟨m1, e1⟩ := (vc_node_trL hB.2.1 hB.2.2.2 hn hz.1.q1 hz.1.qB hr1 hL).2 hm hd1
      refine ⟨⟨a1, hr1⟩, ⟨vi_nz hαE hα1 hz.1.q1 hz.1.qB m1 hr1
        (by rw [← e1]; exact lt_of_le_of_lt le_add_self hrb), az⟩, ?_, fun _ => trivial, fun _ => trivial,
        fun _ => Iff.rfl⟩
      show vt τ (Om1 * q + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r))) = vt (Dl τ n) (Om1 * q + ev (Dl τ n) r)
      rw [hev]; exact e1
    · -- some leaf `≥ α`: `Vc.vc_node_trH` (ii)
      rw [vtr_thc_hi hL] at hl hw hz hd ⊢
      obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn r hl hw.1 hz.2 hd.2 hh hla
      have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2
      have hm := hz.1.mem
      have hrb := hz.1.rb
      have hd1 : vt τ (Om1 * q + ev τ (vtr (Dl τ n) r)) < Dp τ n := hd.1
      rw [a2] at hm hrb hd1
      obtain ⟨m1, e1⟩ := (vc_node_trH hB.2.1 hB.2.2.2 hn hz.1.q1 hz.1.qB hr1 hL).2 hm hd1
      refine ⟨⟨a1, hr1⟩, ⟨vi_nz hαE hα1 hz.1.q1 hz.1.qB m1 hr1 (by rw [← e1]; exact hrb), az⟩, ?_,
        fun _ => trivial, fun _ => trivial, fun _ => Iff.rfl⟩
      show vt τ (Om1 * q + ev τ (vtr (Dl τ n) r)) = vt (Dl τ n) (Om1 * q + ev (Dl τ n) r)
      rw [a2]; exact e1
  | _, .thg m G r, hl, hw, hz, hd, hh, hla => by
    obtain ⟨hτα, hαE, -⟩ := Dl_E hB.2.1 hB.2.2.2 hn
    have hα1 : Dl τ n < Om1 := (Dl_spec hB.2.1 hB.2.2.2 n).2.1
    have hBα : Bases κ (Dl τ n) := ⟨hB.1, hαE, hB.2.2.1.trans hτα, hα1⟩
    by_cases hLo : LoL (Dl τ n) G
    · have hm : m = true := HdD_lo hh.1 hLo
      subst hm
      rw [vtr_thg_lo hLo] at hl hw hz hd ⊢
      obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn r hl.2.2 hw.2.1.2 hz.2.2 hd.2.2.2 hh.2.2 hla.2
      obtain ⟨l1, lz, l2, -, l5, l6⟩ := viTrBB hB hn G hl.1 hw.1 hz.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_vtr _ G).1 hw.2.2.gs
      have hnf : FNF (Dl τ n) G := l5 hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hdat : Rj.rjDat (Om1 * M) < Dl τ n := by
        rw [← hM]; exact urDatLo (InE.pos hαE) G l1 hnf hLo
      have hr1' : Dl τ n + ev (Dl τ n) r < Om1 := by
        have := hw.2.2.r1
        simp only [ev] at this; rwa [a2] at this
      have hr1 : ev (Dl τ n) r < Om1 := lt_of_le_of_lt le_add_self hr1'
      have hev : ev τ (vtr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r)) =
          Om1 * M + (Dl τ n + ev (Dl τ n) r) := by
        simp only [ev]; rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (vtr (Dl τ n) G) + ev τ (UnT.add (.par (Dl τ n)) (vtr (Dl τ n) r))) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      obtain ⟨m1, e1⟩ := (urVt_tr2 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ⟨lz, az⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev]
        refine lt_of_le_of_lt ?_ hw.2.2.rb
        show ev (Dl τ n) r ≤ Dl τ n + ev τ (vtr (Dl τ n) r)
        rw [a2]; exact le_add_self
      · simp only [ev]; rw [l2, a2, hM]; exact e1
    · have hHd : HdM m (Dl τ n) G := HdD_hi hh.1 hLo
      rw [vtr_thg_hi hLo] at hl hw hz hd ⊢
      obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn r hl.2 hw.2.1 hz.2 hd.2.2 hh.2.2 hla.2
      obtain ⟨l1, lz, l2, l4, l5, l6⟩ := viTrBB hB hn G hl.1 hw.1 hz.1 hd.2.1 hh.2.1 hla.1
      have hgs : Gs G := (Gs_vtr _ G).1 hw.2.2.gs
      have hnf : NfM m (Dl τ n) G := NfM_imp l4 l5 m hw.2.2.nf
      obtain ⟨M, hM, hM1⟩ := UnT.ev_dvd (τ := Dl τ n) G hgs
      have hdat := (viDatM hBα m G hla.1 l1 lz hnf hHd).1
      have hME : Om1 * M < Gg.ggE := hM ▸ ev_lt_Er G l1
      have hr1 : ev (Dl τ n) r < Om1 := by rw [← a2]; exact hw.2.2.r1
      have hev : ev τ (vtr (Dl τ n) G) + ev τ (vtr (Dl τ n) r) = Om1 * M + ev (Dl τ n) r := by
        rw [l2, a2, hM]
      have hmem := hw.2.2.mem
      have hlt : vt τ (ev τ (vtr (Dl τ n) G) + ev τ (vtr (Dl τ n) r)) < Dp τ n := hd.1
      rw [hev] at hmem hlt
      rw [hM] at hdat
      obtain ⟨m1, e1⟩ := (ukVt_tr3 hB.2.1 hB.2.2.2 hn hM1 hME hdat hr1).2 hmem hlt
      refine ⟨⟨l1, a1, ⟨hr1, hgs, hnf, hh.1, by rw [hM]; exact m1, ?_, ?_⟩⟩, ⟨lz, az⟩, ?_, fun _ => trivial,
        fun _ => trivial, fun _ => Iff.rfl⟩
      · rw [hM, ← e1, ← hev, ← l6]; exact hw.2.2.bd
      · rw [hM, ← e1, ← hev, ← a2]; exact hw.2.2.rb
      · simp only [ev]; rw [hev, e1, hM]
  | _, .lf c, hl, hw, hz, hd, hh, hla => by
    obtain ⟨a1, az, a2, -⟩ := viTrBB hB hn c hl hw.1 hz hd hh hla
    have h2 : ev τ (vtr (Dl τ n) c) < Om1 := hw.2
    refine ⟨⟨a1, a2 ▸ h2⟩, az, a2, fun _ => trivial, fun _ => trivial, fun V => ?_⟩
    show ev τ (vtr (Dl τ n) c) < V ↔ ev (Dl τ n) c < V
    rw [a2]
  | _, .om b, hl, hw, hz, hd, hh, hla => by
    obtain ⟨a1, az, a2, a4, a5, a6⟩ := viTrBB hB hn b hl hw hz hd hh hla
    refine ⟨a1, az, ?_, a4, a5, a6⟩
    simp only [vtr, ev]; rw [a2]
  | _, .ad x y, hl, hw, hz, hd, hh, hla => by
    obtain ⟨a1, az, a2, a4, a5, a6⟩ := viTrBB hB hn x hl.1 hw.1 hz.1 hd.1 hh.1 hla.1
    obtain ⟨b1, bz, b2, b4, b5, b6⟩ := viTrBB hB hn y hl.2 hw.2 hz.2 hd.2 hh.2 hla.2
    refine ⟨⟨a1, b1⟩, ⟨az, bz⟩, ?_, fun hb => ⟨a4 hb.1, (IsOm_vtr _ x).1 hb.2.1, by rw [← a2, ← b2]; exact hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_vtr _ x).1 hb.2.2.1, by rw [← a2, ← b2]; exact hb.2.2.2⟩,
      fun V => and_congr (a6 V) (b6 V)⟩
    simp only [vtr, ev]; rw [a2, b2]

/-- **`t^τ_α` is correct** (`α = Dl τ n`, `n ≥ 1`): if `vtr α t` has the argument bounds and node conditions over
`τ` with node values below `α⁺`, the decisions `HdD` hold over `α` and the parameters of `t` lie in `T^α`, then `t`
has them over `α` and `(vtr α t)[τ] = t[α]`. -/
theorem viTrB {κ τ : Ordinal.{0}} (hB : Bases κ τ) {n : ℕ} (hn : 1 ≤ n) (t : UnT false)
    (hl : Lv (· ∈ Tset τ) (vtr (Dl τ n) t)) (hw : WFr τ (vtr (Dl τ n) t)) (hz : ZW τ (vtr (Dl τ n) t))
    (hd : Nd τ (· < Dp τ n) (vtr (Dl τ n) t)) (hh : HdDA (Dl τ n) t) (hla : Lv (· ∈ Tset (Dl τ n)) t) :
    WFr (Dl τ n) t ∧ ZW (Dl τ n) t ∧ ev τ (vtr (Dl τ n) t) = ev (Dl τ n) t := by
  obtain ⟨a1, a2, a3, -⟩ := viTrBB hB hn t hl hw hz hd hh hla
  exact ⟨a1, a2, a3⟩

end Googology.Trans.PoR.InaccPsi.R2.Vi
