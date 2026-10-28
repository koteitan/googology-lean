import Googology.Trans.PoR.InaccPsi.R2.UyTerm
import Googology.Trans.PoR.InaccPsi.R2.VcComp

/-!
# The node `thz G r` at every level `G = Ω₁·M < B₂` with parameter leaves: map, membership, base changes

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The term type is `Un.UnT`.  Its node `thc q r` (value `ϑᵗ(Ω₁·q + r[τ])`) is read here as **the node `thz G r` with
the ordinal level `G = Ω₁·q`**, whose countable leaves (`Vc.VcLv`) are parameters: the map `vmap f` moves them,
`vmap f (thc q r) = thc (vq f q) (vmap f r)` with `Ω₁ · vq f q = vcSub f (Ω₁·q)` (`Vc.vcSub`), i.e.
`f (thz G r) = thz (vcSub f G) (f r)`.  When every leaf of `G` is fixed by `f` this is `Un.UnT.map` (`vmap_id`,
`Vc.vcSub_fix`), so the constant levels of `R2.UyTerm` (`Uy.UyLev`, leaves below `κ`) are the special case.

The node conditions (`Nz`, at every `thc`-node, `ZW`): `1 ≤ q`, `Ω₁·q < B₂`, `Ω₁·q ∈ Tᵗ`, `Ω₁·q + ρ ∈ Tᵗ`,
`ρ < ϑᵗ(Ω₁·q + ρ)` (`ρ = r[τ] < Ω₁` is in `Ur.WFr`).  The level leaves (`ZL P`: `VcLv P (Ω₁·q)` at every
`thc`-node) are asked in `Tᵗ[σ]` for the base change.

* `vi_comps_head`, `vi_up_dvd` (**`Ω₁ ∣ π⁻¹ G` for `Ω₁ ∣ G`**: split `π⁻¹ G = Ω₁·k + r` by components,
  `Si.siTB_of_comps`, `R2.pi_add`, `Vc.vc_pi_dvd`), `vi_up_level` (**the inverse image of a level is a level**,
  `Vc.vc_up`, `Vc.vc_up_lt_B`);
* `viMem`, `viHiC_le`, `viDatM`, `viLeB`, `viLe` (membership, the decision `Γ^* ≥ τ`, order);
* `viDownB`, `viDown` (**`π(t[τ; p]) = (vmap π t)[σ]`**, the node case by `Vc.vc_node_img`), `viUpB`, `viUp`,
  `viUp_eq` (**the inverse base change**, the node case by `vi_up_level` and `Vc.vc_node_img`), `viMv` (**the segment
  move**, `Vc.vc_mv` on levels).

New definitions: `vq`, `vmap`, `ZL`, `Nz`, `ZW`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vi

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uh Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Un.UnT Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vc

/-- **The level index after moving the leaves**: `Ω₁ · vq f q = vcSub f (Ω₁·q)` when `Ω₁ ∣ vcSub f (Ω₁·q)`. -/
noncomputable def vq (f : Ordinal.{0} → Ordinal.{0}) (q : Ordinal.{0}) : Ordinal.{0} := vcSub f (Om1 * q) / Om1

/-- **The map on terms moving the parameters and the leaves of the levels** (`thc q r` is `thz (Ω₁·q) r`). -/
noncomputable def vmap (f : Ordinal.{0} → Ordinal.{0}) : {k : Bool} → UnT k → UnT k
  | _, .par p => .par (f p)
  | _, .add s t => .add (vmap f s) (vmap f t)
  | _, .base => .base
  | _, .th1 s => .th1 (vmap f s)
  | _, .thc q r => .thc (vq f q) (vmap f r)
  | _, .thg m G r => .thg m (vmap f G) (vmap f r)
  | _, .lf c => .lf (vmap f c)
  | _, .om b => .om (vmap f b)
  | _, .ad x y => .ad (vmap f x) (vmap f y)

/-- **Every leaf of every level `Ω₁·q` of a `thc`-node satisfies `P`.** -/
def ZL (P : Ordinal.{0} → Prop) : {k : Bool} → UnT k → Prop
  | _, .par _ => True
  | _, .add s t => ZL P s ∧ ZL P t
  | _, .base => True
  | _, .th1 s => ZL P s
  | _, .thc q r => VcLv P (Om1 * q) ∧ ZL P r
  | _, .thg _ G r => ZL P G ∧ ZL P r
  | _, .lf c => ZL P c
  | _, .om b => ZL P b
  | _, .ad x y => ZL P x ∧ ZL P y

/-- **The node conditions of `thz (Ω₁·q) r` over `τ`** (`ρ = r[τ]`). -/
structure Nz (τ q ρ : Ordinal.{0}) : Prop where
  q1 : 1 ≤ q
  qB : Om1 * q < Uc.ucB
  gm : Om1 * q ∈ Tset τ
  mem : Om1 * q + ρ ∈ Tset τ
  rb : ρ < vt τ (Om1 * q + ρ)

/-- The node conditions `Nz` at every `thc`-node. -/
def ZW (τ : Ordinal.{0}) : {k : Bool} → UnT k → Prop
  | _, .par _ => True
  | _, .add s t => ZW τ s ∧ ZW τ t
  | _, .base => True
  | _, .th1 s => ZW τ s
  | _, .thc q r => Nz τ q (ev τ r) ∧ ZW τ r
  | _, .thg _ G r => ZW τ G ∧ ZW τ r
  | _, .lf c => ZW τ c
  | _, .om b => ZW τ b
  | _, .ad x y => ZW τ x ∧ ZW τ y

/-! ## Structural lemmas -/

theorem ZL_mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ x, P x → Q x) : ∀ {k : Bool} (t : UnT k), ZL P t → ZL Q t
  | _, .par _, _ => trivial
  | _, .add s t, h => ⟨ZL_mono hPQ s h.1, ZL_mono hPQ t h.2⟩
  | _, .base, _ => trivial
  | _, .th1 s, h => ZL_mono hPQ s h
  | _, .thc _ r, h => ⟨VcLv_mono (fun x _ hx => hPQ x hx) _ h.1, ZL_mono hPQ r h.2⟩
  | _, .thg _ G r, h => ⟨ZL_mono hPQ G h.1, ZL_mono hPQ r h.2⟩
  | _, .lf c, h => ZL_mono hPQ c h
  | _, .om b, h => ZL_mono hPQ b h
  | _, .ad x y, h => ⟨ZL_mono hPQ x h.1, ZL_mono hPQ y h.2⟩

theorem vq_id (q : Ordinal.{0}) {P : Ordinal.{0} → Prop} (h : VcLv P (Om1 * q)) : vq id q = q := by
  unfold vq
  rw [vcSub_fix _ (VcLv_mono (P := P) (Q := fun x => id x = x) (fun _ _ _ => rfl) _ h)]
  exact Ordinal.mul_div_cancel q Rj.rj_Om1_pos.ne'

/-- **`vmap id` is the identity** on terms whose level leaves satisfy any predicate. -/
theorem vmap_id {P : Ordinal.{0} → Prop} : ∀ {k : Bool} (t : UnT k), ZL P t → vmap id t = t
  | _, .par _, _ => rfl
  | _, .add s t, h => by simp only [vmap, vmap_id s h.1, vmap_id t h.2]
  | _, .base, _ => rfl
  | _, .th1 s, h => by simp only [vmap, vmap_id s h]
  | _, .thc q r, h => by simp only [vmap, vmap_id r h.2, vq_id q h.1]
  | _, .thg _ G r, h => by simp only [vmap, vmap_id G h.1, vmap_id r h.2]
  | _, .lf c, h => by simp only [vmap, vmap_id c h]
  | _, .om b, h => by simp only [vmap, vmap_id b h]
  | _, .ad x y, h => by simp only [vmap, vmap_id x h.1, vmap_id y h.2]

theorem Gs_vmap (f : Ordinal.{0} → Ordinal.{0}) : ∀ {k : Bool} (t : UnT k), Gs (vmap f t) ↔ Gs t
  | _, .par _ => Iff.rfl
  | _, .add _ _ => Iff.rfl
  | _, .base => Iff.rfl
  | _, .th1 _ => Iff.rfl
  | _, .thc _ _ => Iff.rfl
  | _, .thg _ _ _ => Iff.rfl
  | _, .lf _ => Iff.rfl
  | _, .om _ => Iff.rfl
  | _, .ad x y => and_congr (Gs_vmap f x) (Gs_vmap f y)

theorem IsOm_vmap (f : Ordinal.{0} → Ordinal.{0}) : ∀ (t : UnT true), IsOm (vmap f t) ↔ IsOm t
  | .lf _ => Iff.rfl
  | .om _ => Iff.rfl
  | .ad _ _ => Iff.rfl

theorem HiC_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (c : UnT false), Lv (fun p => τ ≤ p → σ ≤ f p) c → HiC τ c → HiC σ (vmap f c)
  | .par _, hl, h => hl h
  | .add s _, hl, h => HiC_vmap s hl.1 h
  | .base, _, _ => trivial
  | .th1 _, _, _ => trivial
  | .thc _ _, _, _ => trivial
  | .thg _ _ _, _, _ => trivial

theorem Hd_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → Hd τ G → Hd σ (vmap f G)
  | .lf c, hl, h => HiC_vmap c hl h
  | .om b, hl, h => Hd_vmap b hl h
  | .ad x _, hl, h => Hd_vmap x hl.1 h

theorem HdE_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → HdE τ G → HdE σ (vmap f G)
  | .lf c, hl, h => HiC_vmap c hl h
  | .om b, hl, h => HdE_vmap b hl h
  | .ad x y, hl, h => h.imp (HdE_vmap x hl.1) (HdE_vmap y hl.2)

theorem HdM_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ (m : Bool) (G : UnT true), Lv (fun p => τ ≤ p → σ ≤ f p) G → HdM m τ G → HdM m σ (vmap f G)
  | false, G, hl, h => Hd_vmap G hl h
  | true, G, hl, h => HdE_vmap G hl h

theorem LoL_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ {k : Bool} (G : UnT k), Lv (fun p => p < τ → f p < σ) G → LoL τ G → LoL σ (vmap f G)
  | _, .lf (.par _), hl, h => hl h
  | _, .om b, hl, h => LoL_vmap b hl h
  | _, .ad x y, hl, h => ⟨LoL_vmap x hl.1 h.1, LoL_vmap y hl.2 h.2⟩
  | _, .lf (.add _ _), _, h => h.elim
  | _, .lf .base, _, h => h.elim
  | _, .lf (.th1 _), _, h => h.elim
  | _, .lf (.thc _ _), _, h => h.elim
  | _, .lf (.thg _ _ _), _, h => h.elim
  | _, .par _, _, h => h.elim
  | _, .add _ _, _, h => h.elim
  | _, .base, _, h => h.elim
  | _, .th1 _, _, h => h.elim
  | _, .thc _ _, _, h => h.elim
  | _, .thg _ _ _, _, h => h.elim

/-- **The decision is carried by a parameter map keeping the order to the base.** -/
theorem HdD_vmap {τ σ : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (m : Bool) (G : UnT true)
    (hl : Lv (fun p => (τ ≤ p → σ ≤ f p) ∧ (p < τ → f p < σ)) G) (h : HdD m τ G) : HdD m σ (vmap f G) :=
  h.imp (HdM_vmap m G (Lv_mono (fun _ hp => hp.1) G hl))
    (fun h' => ⟨h'.1, LoL_vmap G (Lv_mono (fun _ hp => hp.2) G hl) h'.2⟩)

/-! ## The inverse image of a level -/

/-- **The head of a sum keeps its components**: if `ω^e ∣ a` and `y < ω^e`, every component of `a` is a component
of `a + y`. -/
theorem vi_comps_head {e : Ordinal.{0}} :
    ∀ a : Ordinal.{0}, ω ^ e ∣ a → ∀ y, y < ω ^ e → ∀ p ∈ comps a, p ∈ comps (a + y) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha y hy p hp
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [Si.si_comps_zero] at hp; exact absurd hp List.not_mem_nil
  have hay0 : a + y ≠ 0 := fun h => ha0 (le_antisymm (h ▸ le_self_add) zero_le)
  set L := log ω (a + y) with hL
  have hcomps : comps (a + y) = ω ^ L :: comps ((a + y) % ω ^ L) := Si.si_comps_cons hay0
  have hea : ω ^ e ≤ a := Ordinal.le_of_dvd ha0 ha
  have heL : e ≤ L := le_log_of_opow_le one_lt_omega0 (hea.trans le_self_add)
  have hyL : y < ω ^ L := hy.trans_le (opow_le_opow_right omega0_pos heL)
  have hP := isPrincipal_add_omega0_opow L
  have hLa : ω ^ L ≤ a := by
    by_contra hc
    exact absurd (opow_log_le_self ω hay0) (not_le.2 (hP (not_le.1 hc) hyL))
  have hloga : log ω a = L :=
    le_antisymm (log_mono_right ω le_self_add) (le_log_of_opow_le one_lt_omega0 hLa)
  have hpos : (ω : Ordinal.{0}) ^ L ≠ 0 := (opow_pos L omega0_pos).ne'
  set r := a % ω ^ L with hr
  have hrL : r < ω ^ L := Ordinal.mod_lt a hpos
  have hra : r < a := hrL.trans_le hLa
  have hdec : ω ^ L * (a / ω ^ L) + r = a := Ordinal.div_add_mod a _
  have hmod : (a + y) % ω ^ L = r + y := by
    conv_lhs => rw [← hdec, add_assoc]
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (hP hrL hyL)]
  have hdr : ω ^ e ∣ r := by
    have h1 : ω ^ e ∣ ω ^ L * (a / ω ^ L) := dvd_mul_of_dvd_left (opow_dvd_opow ω heL) _
    exact (Ordinal.dvd_add_iff h1).1 (by rw [hdec]; exact ha)
  have hca : comps a = ω ^ L :: comps r := by rw [Si.si_comps_cons ha0, hloga]
  rw [hca] at hp
  rw [hcomps, hmod]
  rcases List.mem_cons.1 hp with rfl | hp
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (IH r hra hdr y hy p hp)

/-- **`Ω₁ ∣ π⁻¹(G)` for a level `G < B₂`, `Ω₁ ∣ G`, `G ∈ T^σ`**: in `π⁻¹ G = Ω₁·k + r` (`r < Ω₁`) both parts lie in
`Tᵗ[σ]` (components), `π(Ω₁·k)` is a multiple of `Ω₁` (`Vc.vc_pi_dvd`) and `π r < Ω₁`, so `G mod Ω₁ = π r`, hence
`π r = 0` and `r = 0`. -/
theorem vi_up_dvd {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hB : G < Uc.ucB) (hG : G ∈ Tset σ) (hd : Om1 ∣ G) :
    Om1 ∣ up σ τ G := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hUB := vc_up_lt_B h hB hG
  set H := up σ τ G with hH
  have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
  have h0T : (0 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt h h0σ
  rcases eq_or_ne H 0 with h0 | h0
  · rw [h0]; exact dvd_zero _
  rcases lt_or_ge H Om1 with hHO | hHO
  · -- `H < Ω₁`: then `G = π H < Ω₁` and `Ω₁ ∣ G` force `G = 0 = π 0`, so `H = 0`
    have hGO : G < Om1 := by rw [← u2]; exact down_lt_Om1 h u1 hHO
    have hG0 : G = 0 := by
      rcases eq_or_ne G 0 with e | e
      · exact e
      · exact absurd (Ordinal.le_of_dvd e hd) (not_le.2 hGO)
    have : H = 0 := (pi_bijOn h).1.injOn u1 h0T (by rw [u2, hG0, pi_lt h h0σ])
    exact absurd this h0
  have hτH : τ ≤ H := (h.2.2.2.le).trans hHO
  set a := Om1 * (H / Om1) with ha
  set r := H % Om1 with hr
  have hr1 : r < Om1 := Ordinal.mod_lt H Rj.rj_Om1_pos.ne'
  have hdec : a + r = H := Ordinal.div_add_mod H Om1
  have hOm : (ω : Ordinal.{0}) ^ (Om1 : Ordinal.{0}) = Om1 := Rj.rj_Om1_opow
  have hda : ω ^ (Om1 : Ordinal.{0}) ∣ a := by rw [hOm]; exact dvd_mul_right _ _
  have hrw : r < ω ^ (Om1 : Ordinal.{0}) := by rw [hOm]; exact hr1
  have haT : a ∈ TB τ σ := Si.siTB_of_comps h u1 hτH (fun p hp => by
    have := vi_comps_head a hda r hrw p hp; rwa [hdec] at this)
  have hrT : r ∈ TB τ σ := Si.siTB_of_comps h u1 hτH (fun p hp => by
    have := Rj.rj_comps_add a hda r hrw p hp; rwa [hdec] at this)
  obtain ⟨-, c2⟩ := pi_add h haT hrT
  have haB : a < Uc.ucB := (le_self_add.trans_eq hdec).trans_lt hUB
  obtain ⟨c, hc⟩ := vc_pi_dvd h a haB haT (dvd_mul_right _ _)
  have hπr : pi σ τ r < Om1 := down_lt_Om1 h hrT hr1
  have hGmod : G % Om1 = pi σ τ r := by
    rw [← u2, ← hdec, c2, hc, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hπr]
  have hπr0 : pi σ τ r = 0 := by rw [← hGmod]; exact Ordinal.dvd_iff_mod_eq_zero.1 hd
  have hr0 : r = 0 := (pi_bijOn h).1.injOn hrT h0T (by rw [hπr0, pi_lt h h0σ])
  exact Ordinal.dvd_iff_mod_eq_zero.2 hr0

/-- **The inverse image of a level is a level**: for `1 ≤ q`, `Ω₁·q < B₂`, `Ω₁·q ∈ T^σ`, the level
`Ω₁ · vq π⁻¹ q = π⁻¹(Ω₁·q)` has `1 ≤ vq π⁻¹ q`, lies below `B₂`, in `Tᵗ[σ]` with all leaves in `Tᵗ[σ]`, and
`π` maps it back to `Ω₁·q`. -/
theorem vi_up_level {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hq1 : 1 ≤ q) (hqB : Om1 * q < Uc.ucB)
    (hG : Om1 * q ∈ Tset σ) :
    Om1 * vq (up σ τ) q = up σ τ (Om1 * q) ∧ 1 ≤ vq (up σ τ) q ∧ Om1 * vq (up σ τ) q < Uc.ucB ∧
      VcLv (· ∈ TB τ σ) (Om1 * vq (up σ τ) q) ∧ Om1 * vq (up σ τ) q ∈ TB τ σ ∧
      pi σ τ (Om1 * vq (up σ τ) q) = Om1 * q := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  obtain ⟨e, hL⟩ := vc_up h hqB hG
  have hUB := vc_up_lt_B h hqB hG
  obtain ⟨k, hk⟩ := vi_up_dvd (τ := τ) h hqB hG (dvd_mul_right _ _)
  have hvq : vq (up σ τ) q = k := by
    unfold vq; rw [← e, hk]; exact Ordinal.mul_div_cancel k Rj.rj_Om1_pos.ne'
  have hk1 : 1 ≤ k := by
    refine Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 ?_)
    rintro rfl
    rw [mul_zero] at hk
    have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
    rw [hk, pi_lt h h0σ] at u2
    have hle : Om1 ≤ Om1 * q := by
      have := mul_le_mul_right hq1 Om1
      rwa [mul_one] at this
    exact (Rj.rj_Om1_pos.trans_le hle).ne' u2.symm
  rw [hvq, ← hk]
  exact ⟨rfl, hk1, hUB, hL, u1, u2⟩

/-! ## Membership, the decision, order -/

/-- `q < B₂` for a node level. -/
theorem nz_q_lt {τ q ρ : Ordinal.{0}} (hz : Nz τ q ρ) : q < Uc.ucB :=
  (le_mul_right q Rj.rj_Om1_pos).trans_lt hz.qB

theorem nz_arg_lt {τ q ρ : Ordinal.{0}} (hz : Nz τ q ρ) (hρ : ρ < Om1) : Om1 * q + ρ < OmTwo :=
  (vc_arg_lt (nz_q_lt hz) hρ).2

theorem viMem {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (t : UnT false), Lv (· ∈ Tset τ) t → WFr τ t → ZW τ t → ev τ t ∈ Tset τ
  | .par _, hl, _, _ => hl
  | .add s t, hl, hw, hz => vzT_add hB.2.1 hB.2.2.2 (viMem hB s hl.1 hw.1 hz.1) (viMem hB t hl.2 hw.2 hz.2)
  | .base, _, _, _ => uh_T_le hB.2.1 hB.2.2.2 le_rfl
  | .th1 s, hl, hw, hz => by
    have hτ1 := hB.2.2.2
    have h1 : (1 : Ordinal.{0}) ∈ Tset τ := uh_T_le hB.2.1 hτ1 (Ub.ub_one_lt hB.2.1).le
    have hO : (1 : Ordinal.{0}) < Om1 := (Ub.ub_one_lt hB.2.1).trans hτ1
    exact (vt_mem hB.2.1 hτ1 (vzT_add hB.2.1 hτ1 h1 (viMem hB s hl hw.1 hz)) (Om1_add_lt hO hw.2)).1
  | .thc _ _, _, hw, hz => (vt_memTwo hB.2.1 hB.2.2.2 hz.1.mem (nz_arg_lt hz.1 hw.2)).1
  | .thg _ G _, _, hw, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).1

/-- **A high countable term is `≥ τ`.** -/
theorem viHiC_le {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (c : UnT false), Lv (· ∈ Tset τ) c → WFr τ c → ZW τ c → HiC τ c → τ ≤ ev τ c
  | .par _, _, _, _, h => h
  | .add s _, hl, hw, hz, h => by
    simp only [ev]; exact (viHiC_le hB s hl.1 hw.1 hz.1 h).trans le_self_add
  | .base, _, _, _, _ => le_rfl
  | .th1 s, _, hw, _, _ => by
    simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
    exact le_self_add.trans (Se.se_wbar_gt _).le
  | .thc _ _, _, hw, hz, _ => (vt_memTwo hB.2.1 hB.2.2.2 hz.1.mem (nz_arg_lt hz.1 hw.2)).2.1
  | .thg _ G _, _, hw, _, _ =>
    (vt_memTwo hB.2.1 hB.2.2.2 hw.2.2.mem (Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1)).2.1

/-- **The decision `Γ^{*τ} ≥ τ` in the head mode.** -/
theorem viDatHb {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → ZW τ G → HbS τ G → Hd τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hz, _, hd => by
    have h1 : τ ≤ ev τ c := viHiC_le hB c hl hw.1 hz hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hz, hb, hd => by
    obtain ⟨h1, h2⟩ := viDatHb hB b hl hw hz hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hz, hb, hd => by
    obtain ⟨h1, h2⟩ := viDatHb hB b hl.1 hw.1 hz.1 hb.1 hd
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2
    have := Uk.UkL.dat_om_add h2 hbE hy
    simp only [ev]
    exact ⟨h1.trans this,
      (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in the normal-form mode.** -/
theorem viDatFN {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → ZW τ G → FNF τ G → HdE τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | .lf c, hl, hw, hz, _, hd => by
    have h1 : τ ≤ ev τ c := viHiC_le hB c hl hw.1 hz hd
    simp only [ev]
    rw [Rj.rjDat_small hw.2]
    exact ⟨h1, ((InE.pos hB.2.1).trans_le h1).ne'⟩
  | .om b, hl, hw, hz, hb, hd => by
    obtain ⟨h1, h2⟩ := viDatFN hB b hl hw hz hb hd
    have hbE := ev_lt_Er b hw
    have := Uk.UkL.dat_om_add (y := 0) h2 hbE (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos))
    rw [add_zero] at this
    simp only [ev]
    exact ⟨h1.trans this, (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)).ne'⟩
  | .ad (.om b) y, hl, hw, hz, hb, hd => by
    have hbE := ev_lt_Er b hw.1
    have hy : ev τ y < Om1 * ω ^ (ev τ b + 1) := by rw [← Uk.UkL.om_mul_omega]; exact hb.2.2.2
    have hne : ev τ (UnT.ad (UnT.om b) y) ≠ 0 := by
      simp only [ev]
      exact (lt_of_lt_of_le (mul_pos Rj.rj_Om1_pos (opow_pos _ omega0_pos)) le_self_add).ne'
    rcases hd with hd | hd
    · obtain ⟨h1, h2⟩ := viDatFN hB b hl.1 hw.1 hz.1 hb.1 hd
      have := Uk.UkL.dat_om_add h2 hbE hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
    · obtain ⟨h1, h2⟩ := viDatFN hB y hl.2 hw.2 hz.2 hb.2.1 hd
      have := dat_om_add_r hbE h2 hy
      exact ⟨by simp only [ev]; exact h1.trans this, hne⟩
  | .ad (.lf _) _, _, _, _, hb, _ => hb.2.2.1.elim
  | .ad (.ad _ _) _, _, _, _, hb, _ => hb.2.2.1.elim

/-- **The decision `Γ^{*τ} ≥ τ` in either mode.** -/
theorem viDatM {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ (m : Bool) (G : UnT true), Lv (· ∈ Tset τ) G → WFr τ G → ZW τ G → NfM m τ G → HdM m τ G →
      τ ≤ Rj.rjDat (ev τ G) ∧ ev τ G ≠ 0
  | false, G, hl, hw, hz, hn, hd => viDatHb hB G hl hw hz hn hd
  | true, G, hl, hw, hz, hn, hd => viDatFN hB G hl hw hz hn hd

/-- **Every parameter and every node value is `≤` the value.** -/
theorem viLeB {κ τ : Ordinal.{0}} (hB : Bases κ τ) :
    ∀ {k : Bool} (t : UnT k), Lv (· ∈ Tset τ) t → WFr τ t → ZW τ t → ∀ V : Ordinal.{0},
      (k = false → ev τ t ≤ V) → Lf (fun c => ev τ c ≤ V) t → Lv (· ≤ V) t ∧ Nd τ (· ≤ V) t
  | _, .par _, _, _, _, _, hv, _ => ⟨hv rfl, trivial⟩
  | _, .add s t, hl, hw, hz, V, hv, _ => by
    have hs : ev τ s ≤ V := le_self_add.trans (hv rfl)
    have ht : ev τ t ≤ V := le_add_self.trans (hv rfl)
    obtain ⟨a1, a2⟩ := viLeB hB s hl.1 hw.1 hz.1 V (fun _ => hs) (Lf_cnt _ s)
    obtain ⟨b1, b2⟩ := viLeB hB t hl.2 hw.2 hz.2 V (fun _ => ht) (Lf_cnt _ t)
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩
  | _, .base, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _, .th1 s, hl, hw, hz, V, hv, _ => by
    have hle : ev τ s ≤ ev τ (.th1 s) := by
      simp only [ev]; rw [vt_wbar hB.2.1 hB.2.2.2 hw.2]
      exact le_add_self.trans (Se.se_wbar_gt _).le
    exact viLeB hB s hl hw.1 hz V (fun _ => hle.trans (hv rfl)) (Lf_cnt _ s)
  | _, .thc q r, hl, hw, hz, V, hv, _ => by
    have hlt : ev τ r < ev τ (.thc q r) := hz.1.rb
    obtain ⟨a1, a2⟩ := viLeB hB r hl hw.1 hz.2 V (fun _ => hlt.le.trans (hv rfl)) (Lf_cnt _ r)
    exact ⟨a1, hv rfl, a2⟩
  | _, .thg m G r, hl, hw, hz, V, hv, _ => by
    have hvV : ev τ (UnT.thg m G r) ≤ V := hv rfl
    obtain ⟨a1, a2⟩ := viLeB hB r hl.2 hw.2.1 hz.2 V (fun _ => hw.2.2.rb.le.trans hvV) (Lf_cnt _ r)
    obtain ⟨l1, l2⟩ := viLeB hB G hl.1 hw.1 hz.1 V (fun h => nomatch h)
      (Lf_mono (fun c hc => hc.le.trans hvV) G hw.2.2.bd)
    exact ⟨⟨l1, a1⟩, ⟨hvV, l2, a2⟩⟩
  | _, .lf c, hl, hw, hz, V, _, hc => viLeB hB c hl hw.1 hz V (fun _ => hc) (Lf_cnt _ c)
  | _, .om b, hl, hw, hz, V, _, hc => viLeB hB b hl hw hz V (fun h => nomatch h) hc
  | _, .ad x y, hl, hw, hz, V, _, hc => by
    obtain ⟨a1, a2⟩ := viLeB hB x hl.1 hw.1 hz.1 V (fun h => nomatch h) hc.1
    obtain ⟨b1, b2⟩ := viLeB hB y hl.2 hw.2 hz.2 V (fun h => nomatch h) hc.2
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩

theorem viLe {κ τ : Ordinal.{0}} (hB : Bases κ τ) (t : UnT false) (hl : Lv (· ∈ Tset τ) t) (hw : WFr τ t)
    (hz : ZW τ t) : Lv (· ≤ ev τ t) t ∧ Nd τ (· ≤ ev τ t) t :=
  viLeB hB t hl hw hz _ (fun _ => le_rfl) (UnT.Lf_cnt _ t)

/-! ## The base change -/

/-- **The base change on terms of both sorts with moving level leaves**: values, argument bounds, node conditions
(`Ur.Ngr` and `Nz`), the `·ω`-bounds and the leaf bounds are carried by `π_{σ,τ}`; at a node `thz G r` the level
becomes `vcSub π G` (`Vc.vc_node_img`). -/
theorem viDownB {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ {k : Bool} (t : UnT k), WFr τ t → Lv (· ∈ TB τ σ) t → ZW τ t → ZL (· ∈ TB τ σ) t →
      ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (vmap (pi σ τ) t) ∧ WFr σ (vmap (pi σ τ) t) ∧
      ZW σ (vmap (pi σ τ) t) ∧
      (HbS τ t → HbS σ (vmap (pi σ τ) t)) ∧ (FNF τ t → FNF σ (vmap (pi σ τ) t)) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev τ c < V) t → Lf (fun c => ev σ c < pi σ τ V) (vmap (pi σ τ) t))
  | _, .par p, _, hp, _, _ =>
    ⟨hp, rfl, trivial, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', -⟩ := viDownB h s hw.1 hl.1 hz.1 hzl.1
    obtain ⟨b1, b2, b3, b3', -⟩ := viDownB h t hw.2 hl.2 hz.2 hzl.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, ⟨a3', b3'⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, vmap]; rw [c2, a2, b2]
  | _, .base, _, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', -⟩ := viDownB h s hw.1 hl hz hzl
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hlt1 : 1 + ev τ s < Om1 := Om1_add_lt hO hw.2
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by
      show ((Par τ (vt τ (1 + ev τ s)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩, ?_, ⟨a3, ?_⟩,
      a3', fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · simp only [ev, vmap]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
    · rw [← a2]; exact down_lt_Om1 h a1 hw.2
  | _, .thc q r, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', -⟩ := viDownB h r hw.1 hl hz.2 hzl.2
    obtain ⟨n1, M', hM', hM1, hMB, hρ1, hpv⟩ := vc_node_img h hz.1.q1 hz.1.qB hzl.1 a1 hw.2
    have hvq : vq (pi σ τ) q = M' := by
      unfold vq; rw [← hM']; exact Ordinal.mul_div_cancel M' Rj.rj_Om1_pos.ne'
    obtain ⟨hGT, hGpi⟩ := vc_pi h _ hz.1.qB hzl.1
    obtain ⟨c1, c2⟩ := pi_add h hGT a1
    have hG' : pi σ τ (Om1 * q) = Om1 * M' := by rw [hGpi, hM']
    refine ⟨n1, ?_, ⟨a3, ?_⟩, ⟨?_, a3'⟩, fun _ => trivial, fun _ => trivial, fun _ _ _ => trivial⟩
    · show pi σ τ (vt τ (Om1 * q + ev τ r)) = vt σ (Om1 * vq (pi σ τ) q + ev σ (vmap (pi σ τ) r))
      rw [hvq, ← a2]; exact hpv
    · show ev σ (vmap (pi σ τ) r) < Om1
      rw [← a2]; exact hρ1
    · show Nz σ (vq (pi σ τ) q) (ev σ (vmap (pi σ τ) r))
      rw [hvq, ← a2]
      refine ⟨hM1, hMB, ?_, ?_, ?_⟩
      · rw [← hG']; exact (pi_bijOn h).1.mapsTo hGT
      · rw [← hG', ← c2]; exact (pi_bijOn h).1.mapsTo c1
      · rw [← hpv]; exact (pi_bijOn h).2 a1 n1 hz.1.rb
  | _, .thg m G r, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', -⟩ := viDownB h r hw.2.1 hl.2 hz.2 hzl.2
    obtain ⟨g1, g2, g3, g3', g4, g5, g6⟩ := viDownB h G hw.1 hl.1 hz.1 hzl.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er G hw.1) hw.2.2.r1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ G + ev τ r) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ G + ev τ r)) : Set Ordinal.{0})) ⊆ Set.Iio σ; rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ G + ev τ r)) =
        vt σ (ev σ (vmap (pi σ τ) G) + ev σ (vmap (pi σ τ) r)) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, vmap]; exact hpv, ⟨g3, a3, ?_⟩, ⟨g3', a3'⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    refine ⟨by rw [← a2]; exact down_lt_Om1 h a1 hw.2.2.r1, (Gs_vmap _ G).2 hw.2.2.gs,
      NfM_imp g4 g5 m hw.2.2.nf,
      HdD_vmap m G (Lv_mono (fun p hp => ⟨fun hτp => down_ge h hp hτp, fun hpτ => by
        have hpσ := (TB_inter_lt h hpτ).1 hp
        rw [pi_lt h hpσ]; exact hpσ⟩) G hl.1) hw.2.2.hd,
      by rw [← g2, ← a2, ← c2]; exact (pi_bijOn h).1.mapsTo c1, ?_, ?_⟩
    · rw [← hpv]; exact g6 _ hVT hw.2.2.bd
    · rw [← hpv, ← a2]; exact (pi_bijOn h).2 a1 hVT hw.2.2.rb
  | _, .lf c, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', -⟩ := viDownB h c hw.1 hl hz hzl
    refine ⟨a1, a2, ⟨a3, by rw [← a2]; exact down_lt_Om1 h a1 hw.2⟩, a3', fun _ => trivial,
      fun _ => trivial, fun V hV hc => ?_⟩
    show ev σ (vmap (pi σ τ) c) < pi σ τ V
    rw [← a2]; exact (pi_bijOn h).2 a1 hV hc
  | _, .om b, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', a4, a5, a6⟩ := viDownB h b hw hl hz hzl
    have hbE := ev_lt_Er b hw
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a3', a4, a5, a6⟩
    simp only [ev, vmap]; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hz, hzl => by
    obtain ⟨a1, a2, a3, a3', a4, a5, a6⟩ := viDownB h x hw.1 hl.1 hz.1 hzl.1
    obtain ⟨b1, b2, b3, b3', b4, b5, b6⟩ := viDownB h y hw.2 hl.2 hz.2 hzl.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev τ y < ev τ x * ω → ev σ (vmap (pi σ τ) y) < ev σ (vmap (pi σ τ) x) * ω := by
      intro hlt; rw [← a2, ← b2]; exact (unPi_lt_mul_omega_iff h a1 b1).1 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, ⟨a3', b3'⟩, fun hb => ⟨a4 hb.1, (IsOm_vmap _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_vmap _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, vmap]; rw [c2, a2, b2]

/-- **The base change on terms**: `π_{σ,τ}(t[τ; p]) = (vmap π t)[σ]` (parameters and level leaves moved by `π`). -/
theorem viDown {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UnT false) (hw : WFr τ t) (hl : Lv (· ∈ TB τ σ) t)
    (hz : ZW τ t) (hzl : ZL (· ∈ TB τ σ) t) :
    ev τ t ∈ TB τ σ ∧ pi σ τ (ev τ t) = ev σ (vmap (pi σ τ) t) ∧ WFr σ (vmap (pi σ τ) t) ∧
      ZW σ (vmap (pi σ τ) t) := by
  obtain ⟨a1, a2, a3, a4, -⟩ := viDownB h t hw hl hz hzl
  exact ⟨a1, a2, a3, a4⟩

/-- **The inverse base change on terms of both sorts with moving level leaves** (the node case by
`vi_up_level` and `Vc.vc_node_img`). -/
theorem viUpB {σ τ : Ordinal.{0}} (h : Bases σ τ) :
    ∀ {k : Bool} (t : UnT k), WFr σ t → Lv (· ∈ Tset σ) t → ZW σ t →
      ev τ (vmap (up σ τ) t) ∈ TB τ σ ∧ pi σ τ (ev τ (vmap (up σ τ) t)) = ev σ t ∧
      WFr τ (vmap (up σ τ) t) ∧ ZW τ (vmap (up σ τ) t) ∧ ZL (· ∈ TB τ σ) (vmap (up σ τ) t) ∧
      (HbS σ t → HbS τ (vmap (up σ τ) t)) ∧ (FNF σ t → FNF τ (vmap (up σ τ) t)) ∧
      (∀ V ∈ TB τ σ, Lf (fun c => ev σ c < pi σ τ V) t → Lf (fun c => ev τ c < V) (vmap (up σ τ) t))
  | _, .par p, _, hp, _ =>
    ⟨(up_spec h hp).1, (up_spec h hp).2, trivial, trivial, trivial, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
  | _, .add s t, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', -⟩ := viUpB h s hw.1 hl.1 hz.1
    obtain ⟨b1, b2, b3, b3', b3'', -⟩ := viUpB h t hw.2 hl.2 hz.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    refine ⟨c1, ?_, ⟨a3, b3⟩, ⟨a3', b3'⟩, ⟨a3'', b3''⟩, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
    simp only [ev, vmap] at c2 ⊢; rw [c2, a2, b2]
  | _, .base, _, _, _ =>
    ⟨(pi_base h).1, (pi_base h).2, trivial, trivial, trivial, fun _ => trivial, fun _ => trivial,
      fun _ _ _ => trivial⟩
  | _, .th1 s, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', -⟩ := viUpB h s hw.1 hl hz
    have hσ1 : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
    have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := (TB_inter_lt h (hσ1.trans h.2.2.1)).2 hσ1
    have hO : (1 : Ordinal.{0}) < Om1 := hσ1.trans (h.2.2.1.trans h.2.2.2)
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨c1, c2⟩ := pi_add h h1T a1
    have hlt1 : 1 + ev τ (vmap (up σ τ) s) < Om1 := Om1_add_lt hO hy1
    obtain ⟨d1, d2⟩ := vt_mem h.2.1 h.2.2.2 c1.1 hlt1
    refine ⟨⟨d1, by simp only [ev, vmap]; rw [d2]; exact c1.2⟩, ?_, ⟨a3, hy1⟩, a3', a3'', fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    simp only [ev, vmap]; rw [pi_vt h c1 hlt1, c2, pi_lt h hσ1, a2]
  | _, .thc q r, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', -⟩ := viUpB h r hw.1 hl hz.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2
    obtain ⟨u0, u1, u2, u3, u4, u5⟩ := vi_up_level (τ := τ) h hz.1.q1 hz.1.qB hz.1.gm
    obtain ⟨n1, M', hM', -, -, -, hpv⟩ := vc_node_img h u1 u2 u3 a1 hy1
    have hM'q : Om1 * M' = Om1 * q := by rw [hM', ← vc_pi_TB h u2 u4, u5]
    obtain ⟨c1, c2⟩ := pi_add h u4 a1
    have hpv' : pi σ τ (vt τ (Om1 * vq (up σ τ) q + ev τ (vmap (up σ τ) r))) = vt σ (Om1 * q + ev σ r) := by
      rw [hpv, hM'q, a2]
    refine ⟨n1, hpv', ⟨a3, hy1⟩, ⟨⟨u1, u2, u4.1, c1.1, ?_⟩, a3'⟩, ⟨u3, a3''⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    have hb := hz.1.rb
    rw [← hpv', ← a2] at hb
    exact ((pi_bijOn h).2.lt_iff_lt a1 n1).1 hb
  | _, .thg m G r, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', -⟩ := viUpB h r hw.2.1 hl.2 hz.2
    have hy1 := unUp_lt_Om1 h a1 a2 hw.2.2.r1
    obtain ⟨g1, g2, g3, g3', g3'', g4, g5, g6⟩ := viUpB h G hw.1 hl.1 hz.1
    obtain ⟨c1, c2⟩ := pi_add h g1 a1
    have hlt2 := Uk.arg_lt2 (ev_lt_Er _ g3) hy1
    obtain ⟨d1, -, -, -, d2⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hlt2
    have hVT : vt τ (ev τ (vmap (up σ τ) G) + ev τ (vmap (up σ τ) r)) ∈ TB τ σ := ⟨d1, by
      show ((Par τ (vt τ (ev τ (vmap (up σ τ) G) + ev τ (vmap (up σ τ) r)))) : Set Ordinal.{0}) ⊆ Set.Iio σ
      rw [d2]; exact c1.2⟩
    have hpv : pi σ τ (vt τ (ev τ (vmap (up σ τ) G) + ev τ (vmap (up σ τ) r))) = vt σ (ev σ G + ev σ r) := by
      rw [pi_vt_two h c1 hlt2, c2, g2, a2]
    refine ⟨hVT, by simp only [ev, vmap]; exact hpv, ⟨g3, a3, ?_⟩, ⟨g3', a3'⟩, ⟨g3'', a3''⟩, fun _ => trivial,
      fun _ => trivial, fun _ _ _ => trivial⟩
    refine ⟨hy1, (Gs_vmap _ G).2 hw.2.2.gs, NfM_imp g4 g5 m hw.2.2.nf,
      HdD_vmap m G (Lv_mono (fun p hp => ⟨fun hσp => up_ge h hp hσp, fun hpσ => by
        rw [up_lt h hpσ]; exact hpσ.trans h.2.2.1⟩) G hl.1) hw.2.2.hd, c1.1, ?_, ?_⟩
    · have hb := hw.2.2.bd
      rw [← hpv] at hb
      exact g6 _ hVT hb
    · have hb := hw.2.2.rb
      rw [← hpv, ← a2] at hb
      by_contra hge
      have := ((pi_bijOn h).2.le_iff_le hVT a1).2 (not_lt.1 hge)
      exact absurd hb (not_lt.2 this)
  | _, .lf c, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', -⟩ := viUpB h c hw.1 hl hz
    refine ⟨a1, a2, ⟨a3, unUp_lt_Om1 h a1 a2 hw.2⟩, a3', a3'', fun _ => trivial, fun _ => trivial,
      fun V hV hc => ?_⟩
    show ev τ (vmap (up σ τ) c) < V
    have hc' : ev σ c < pi σ τ V := hc
    rw [← a2] at hc'
    by_contra hge
    have := ((pi_bijOn h).2.le_iff_le hV a1).2 (not_lt.1 hge)
    exact absurd hc' (not_lt.2 this)
  | _, .om b, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', a4, a5, a6⟩ := viUpB h b hw hl hz
    have hbE := ev_lt_Er _ a3
    obtain ⟨o1, o2⟩ := siOm1_opow_TB h hbE
    refine ⟨o1.2 a1, ?_, a3, a3', a3'', a4, a5, a6⟩
    simp only [ev, vmap] at o2 ⊢; rw [o2 a1, a2]
  | _, .ad x y, hw, hl, hz => by
    obtain ⟨a1, a2, a3, a3', a3'', a4, a5, a6⟩ := viUpB h x hw.1 hl.1 hz.1
    obtain ⟨b1, b2, b3, b3', b3'', b4, b5, b6⟩ := viUpB h y hw.2 hl.2 hz.2
    obtain ⟨c1, c2⟩ := pi_add h a1 b1
    have hω : ev σ y < ev σ x * ω → ev τ (vmap (up σ τ) y) < ev τ (vmap (up σ τ) x) * ω := by
      intro hlt; rw [← a2, ← b2] at hlt; exact (unPi_lt_mul_omega_iff h a1 b1).2 hlt
    refine ⟨c1, ?_, ⟨a3, b3⟩, ⟨a3', b3'⟩, ⟨a3'', b3''⟩, fun hb => ⟨a4 hb.1, (IsOm_vmap _ x).2 hb.2.1, hω hb.2.2⟩,
      fun hb => ⟨a5 hb.1, b5 hb.2.1, (IsOm_vmap _ x).2 hb.2.2.1, hω hb.2.2.2⟩,
      fun V hV hc => ⟨a6 V hV hc.1, b6 V hV hc.2⟩⟩
    simp only [ev, vmap] at c2 ⊢; rw [c2, a2, b2]

/-- **The inverse base change on terms.** -/
theorem viUp {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UnT false) (hw : WFr σ t) (hl : Lv (· ∈ Tset σ) t)
    (hz : ZW σ t) :
    ev τ (vmap (up σ τ) t) ∈ TB τ σ ∧ pi σ τ (ev τ (vmap (up σ τ) t)) = ev σ t ∧ WFr τ (vmap (up σ τ) t) ∧
      ZW τ (vmap (up σ τ) t) ∧ ZL (· ∈ TB τ σ) (vmap (up σ τ) t) := by
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := viUpB h t hw hl hz
  exact ⟨a1, a2, a3, a4, a5⟩

/-- `π_{σ,τ}⁻¹(t[σ; p]) = (vmap π⁻¹ t)[τ]`. -/
theorem viUp_eq {σ τ : Ordinal.{0}} (h : Bases σ τ) (t : UnT false) (hw : WFr σ t) (hl : Lv (· ∈ Tset σ) t)
    (hz : ZW σ t) :
    up σ τ (ev σ t) = ev τ (vmap (up σ τ) t) ∧ WFr τ (vmap (up σ τ) t) ∧ ZW τ (vmap (up σ τ) t) := by
  obtain ⟨a1, a2, a3, a4, -⟩ := viUp h t hw hl hz
  exact ⟨by rw [← a2]; exact up_pi h a1, a3, a4⟩

/-- **The segment move on terms**: `mv b c (t[b; p]) = (vmap (mv b c) t)[c]`, the level leaves moved too. -/
theorem viMv {κ b c : Ordinal.{0}} (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1) (hκb : κ ≤ b)
    (hκc : κ ≤ c) (t : UnT false) (hw : WFr b t) (hz : ZW b t) (hl : Lv (· ∈ TB b κ) t)
    (hzl : ZL (· ∈ TB b κ) t) :
    mv b c (ev b t) = ev c (vmap (mv b c) t) ∧ WFr c (vmap (mv b c) t) ∧ ZW c (vmap (mv b c) t) := by
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    have hB : Bases c b := ⟨hc, hb, hcb, hb1⟩
    obtain ⟨-, a2, a3, a4⟩ := viDown hB t hw (Lv_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hl) hz
      (ZL_mono (fun p hp => Ub.ub_TB_mono hκc hp) t hzl)
    rw [hmv]; exact ⟨a2, a3, a4⟩
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv, vmap_id t hzl]; exact ⟨rfl, hw, hz⟩
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    have hB : Bases b c := ⟨hb, hc, hbc, hc1⟩
    rw [hmv]
    exact viUp_eq hB t hw (Lv_mono (fun p hp => hp.1) t hl) hz

end Googology.Trans.PoR.InaccPsi.R2.Vi
