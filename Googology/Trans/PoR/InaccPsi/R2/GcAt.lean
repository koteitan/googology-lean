import Googology.Trans.PoR.InaccPsi.R2.GbAt
import Googology.Trans.PoR.InaccPsi.R2.GbLim

/-!
# One atom set for every constant offset: `ψ_{Ω₂}(α) = Γ_{Ω₁+1+α}`, `α < ε₀`

`R2.GaAt` has the atoms `Γ_{Ω₁+1+k}`, `R2.GbAt` adds `Γ_{Ω₁+ω+k}`; each limit needed a new atom set.  Here one set for
every constant offset at once:

* `gcG` (**the enumeration of the strongly critical ordinals above `Ω₁`**: `gcG α = Γ_{Ω₁+1+α}`), `gcV = gcG ε₀`,
  `gcAt = {gcG α | α < ε₀}`;
* `gc_cst_mem` (**every `α < ε₀` lies in every hull `Cl(a, b)`**), `gc_cst` (**every `α < ε₀` is a constant**: below
  every `ε`-number), `gc_psi` (**`ψ_{Ω₂}(α) = gcG α` for `α ≤ ε₀`**), `gcG_limit` (**`gcG` is continuous**), `gc_cQs`
  (**`cQs (gcG α) = gcG (α+1)`**), `gcSC_cases` (**every strongly critical `s ∈ (Ω₁, gcV)` is an atom**);
* the codes `GxCl Z gcAt`: `gcCl_lt_V`, `gcCl_mem_CSet`, `gcCl_of_CSet` (**the hull below `gcV` consists of codes**),
  `ga_of_gcCl` / `gc_of_gaCl` / `gcTh_eq_gaTh` (**below `Γ_{Ω₁+ω}` the codes and readings are those of `R2.GaCl`**);
* the readings: `gcTh_iSup` (**the reading is continuous** along any small family), `gcTh_limit`, `gcTh_At` (**the
  reading of every atom is strongly critical, in `(y, Ω₁)`**), `gcTh_lt_Om1`;
* `GcPoly X E` (terms for the codes below `E`), `gcPoly_of_SC`, `gcPoly_of_ga`.

No new axiom.  New definitions: `gcSet`, `gcG`, `gcV`, `gcAt`, `GcPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## Constants -/

/-- **`ε₀` is below every `ε`-number.** -/
theorem gc_eps0_le {x : Ordinal.{0}} (hx : InE x) : ε₀ ≤ x := epsilon_zero_le_of_omega0_opow_le hx.le

theorem gc_eps0_le_Om1 : ε₀ ≤ Om (1 : Ordinal.{0}) := epsilon_zero_le_of_omega0_opow_le Bt.Om1_opow.le

theorem gc_eps0_lim : IsSuccLimit (ε₀ : Ordinal.{0}) := by
  have h := ph_opow_lim (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- **Every `α < ε₀` is a constant**: below every `ε`-number. -/
theorem gc_cst {α : Ordinal.{0}} (h : α < ε₀) : Gb.GqCst α := fun _ hx => h.trans_le (gc_eps0_le hx)

theorem gc_log_lt {α : Ordinal.{0}} (h0 : α ≠ 0) (h : α < ε₀) : log ω α < α := by
  refine lt_of_le_of_ne (log_le_self ω α) fun e => ?_
  have h1 : ω ^ α ≤ α := by
    have := opow_log_le_self ω h0
    rwa [e] at this
  exact absurd (epsilon_zero_le_of_omega0_opow_le h1) (not_le.2 h)

variable {S : InaccSeq.{0}}

/-- **Every `α < ε₀` lies in every hull `Cl(a, b)`.** -/
theorem gc_cst_mem (a b : Ordinal.{0}) : ∀ α : Ordinal.{0}, α < ε₀ → α ∈ S.CSet a b := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  rcases eq_or_ne α 0 with rfl | h0
  · exact CSet.zero_mem _ _
  have hL := gc_log_lt h0 hα
  have hw : ω ^ log ω α ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (IH _ hL (hL.trans hα))
    rwa [veblen_zero_apply] at this
  have hwd : ω ^ log ω α ≤ α := opow_log_le_self ω h0
  have hdr : ω ^ log ω α + (α - ω ^ log ω α) = α := Ordinal.add_sub_cancel_of_le hwd
  rcases (Ordinal.sub_le_self α (ω ^ log ω α)).lt_or_eq with hrd | hrd
  · rw [← hdr]; exact CSet.add_mem hw (IH _ hrd (hrd.trans hα))
  · exfalso
    have h1 : ω ^ log ω α + α = α := by conv_rhs => rw [← hdr]
                                        rw [hrd]
    have h2 := add_eq_right_iff_mul_omega0_le.1 h1
    rw [← opow_succ] at h2
    exact absurd (lt_opow_succ_log_self one_lt_omega0 α) (not_lt.2 h2)

theorem gc_countable {α : Ordinal.{0}} (h : α < Om (1 : Ordinal.{0})) : Countable (Iio α) := by
  have h' : α < (Cardinal.aleph 1).ord := by
    rw [← ph_Om1_eq] at h
    simpa [Om1, Ordinal.omega, Cardinal.ord_aleph] using h
  have hc : (Iio α).Countable := by
    have h2 : α.card ≤ Cardinal.aleph0 := by simpa using Cardinal.lt_ord.1 h'
    refine Cardinal.le_aleph0_iff_set_countable.1 ?_
    rw [Cardinal.mk_Iio_ordinal]
    exact Cardinal.lift_le_aleph0.2 h2
  exact hc.to_subtype

/-! ## The enumeration of the strongly critical ordinals above `Ω₁` -/

/-- The strongly critical ordinals above `Ω₁`. -/
def gcSet : Set Ordinal.{0} := {b | SC b ∧ Om 1 < b}

/-- **`gcG α = Γ_{Ω₁+1+α}`**: the `α`-th strongly critical ordinal above `Ω₁`. -/
noncomputable def gcG : Ordinal.{0} → Ordinal.{0} := enumOrd gcSet

/-- **`Γ_{Ω₁+ε₀}`**: the bound of the codes. -/
noncomputable def gcV : Ordinal.{0} := gcG ε₀

/-- **The atoms**: `gcG α` for every constant `α < ε₀`. -/
def gcAt : Set Ordinal.{0} := {s | ∃ α, α < ε₀ ∧ s = gcG α}

/-- **A supremum of strongly critical ordinals is strongly critical.** -/
theorem gc_SC_iSup {ι : Type*} [Small.{0} ι] [Nonempty ι] {f : ι → Ordinal.{0}} (hf : ∀ i, SC (f i)) :
    SC (⨆ i, f i) := by
  have hbdd : BddAbove (range f) := Ordinal.bddAbove_of_small
  obtain ⟨i0⟩ := ‹Nonempty ι›
  refine ⟨lt_of_lt_of_le (hf i0).1 (le_ciSup hbdd i0), fun x hx y hy => ?_⟩
  obtain ⟨i, hi⟩ := (lt_ciSup_iff hbdd).1 hx
  obtain ⟨j, hj⟩ := (lt_ciSup_iff hbdd).1 hy
  rcases le_total (f i) (f j) with h | h
  · exact ((hf j).2 x (hi.trans_le h) y hj).trans_le (le_ciSup hbdd j)
  · exact ((hf i).2 x hi y (hj.trans_le h)).trans_le (le_ciSup hbdd i)

theorem gcSet_unbdd : ¬ BddAbove gcSet := by
  rintro ⟨b, hb⟩
  set c := max b (Om 1) with hc
  have hS : cQs c ∈ gcSet :=
    ⟨cQs_SC c, (le_max_right b (Om 1)).trans_lt (cQ_lt_cQs c 0)⟩
  exact absurd (hb hS) (not_le.2 ((le_max_left b (Om 1)).trans_lt (cQ_lt_cQs c 0)))

theorem gcG_mem (α : Ordinal.{0}) : gcG α ∈ gcSet := enumOrd_mem gcSet_unbdd α

theorem gcG_SC (α : Ordinal.{0}) : SC (gcG α) := (gcG_mem α).1

theorem gcG_Om1_lt (α : Ordinal.{0}) : Om 1 < gcG α := (gcG_mem α).2

theorem gcG_strictMono : StrictMono gcG := enumOrd_strictMono gcSet_unbdd

theorem gcG_lt {α β : Ordinal.{0}} (h : α < β) : gcG α < gcG β := gcG_strictMono h

theorem gcG_le {α β : Ordinal.{0}} (h : α ≤ β) : gcG α ≤ gcG β := gcG_strictMono.monotone h

theorem gcG_lt_iff {α β : Ordinal.{0}} : gcG α < gcG β ↔ α < β := gcG_strictMono.lt_iff_lt

/-- **`gcG α` is at most every strongly critical `b > Ω₁` above every `gcG β`, `β < α`.** -/
theorem gcG_le_of {α b : Ordinal.{0}} (hb : SC b) (hOb : Om 1 < b) (h : ∀ β < α, gcG β < b) : gcG α ≤ b :=
  enumOrd_le_of_forall_lt ⟨hb, hOb⟩ h

/-- **`gcG` is continuous**: `gcG λ = sup_{β<λ} gcG β` at a limit `λ`. -/
theorem gcG_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : gcG l = ⨆ β : Iio l, gcG β.1 := by
  haveI : Nonempty (Iio l) := ⟨⟨0, hl.bot_lt⟩⟩
  have hbdd : BddAbove (range fun β : Iio l => gcG β.1) := Ordinal.bddAbove_of_small
  refine le_antisymm (gcG_le_of (gc_SC_iSup fun β => gcG_SC β.1) ?_ fun β hβ => ?_)
    (ciSup_le' fun β => gcG_le β.2.le)
  · exact (gcG_Om1_lt 0).trans_le (le_ciSup hbdd ⟨0, hl.bot_lt⟩)
  · exact (gcG_lt (lt_add_one β)).trans_le (le_ciSup hbdd ⟨β + 1, hl.add_one_lt hβ⟩)

theorem gcG_lt_of_lt_limit {l e : Ordinal.{0}} (hl : IsSuccLimit l) (he : e < gcG l) : ∃ β < l, e < gcG β := by
  rw [gcG_limit hl] at he
  obtain ⟨β, hβ⟩ := Ordinal.lt_iSup_iff.1 he
  exact ⟨β.1, β.2, hβ⟩

/-- **`cQs c = gcG (α+1)`** for `gcG α ≤ c < gcG (α+1)`. -/
theorem gc_cQs_of {α c : Ordinal.{0}} (h1 : gcG α ≤ c) (h2 : c < gcG (α + 1)) : cQs c = gcG (α + 1) := by
  refine le_antisymm (cQs_min (gcG_SC _) h2) (gcG_le_of (cQs_SC c) ((gcG_Om1_lt α).trans_le
    (h1.trans (cQ_lt_cQs c 0).le)) fun β hβ => ?_)
  exact ((gcG_le (Order.lt_add_one_iff.1 hβ)).trans h1).trans_lt (cQ_lt_cQs c 0)

/-- **`cQs (gcG α) = gcG (α+1)`**: the next strongly critical ordinal. -/
theorem gc_cQs (α : Ordinal.{0}) : cQs (gcG α) = gcG (α + 1) := gc_cQs_of le_rfl (gcG_lt (lt_add_one α))

/-- **`ψ_{Ω₂}(α) = gcG α`** for `α ≤ ε₀`. -/
theorem gc_psi (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, α ≤ ε₀ → S.psi α (Om (1 + 1)) = gcG α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  refine le_antisymm (gaPsi_le S (gcG_SC α) (gcG_Om1_lt α) fun e he => ?_)
    (gcG_le_of (ga_psi_SC α) (ga_Om1_lt_psi α) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hα)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hα)]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) hβ (gc_cst_mem _ _ β (hβ.trans_le hα))

theorem gcG_nat (S : InaccSeq.{0}) (k : ℕ) : gcG (k : Ordinal.{0}) = gaG k := by
  rw [← gc_psi S _ (natCast_lt_epsilon k 0).le, (gaG_spec S k).1]

theorem gcG_omega (S : InaccSeq.{0}) : gcG ω = gaW := by
  rw [← gc_psi S _ (omega0_lt_epsilon 0).le, (gaW_psi S).1]

theorem gcV_psi (S : InaccSeq.{0}) : S.psi ε₀ (Om (1 + 1)) = gcV := gc_psi S _ le_rfl

theorem gcV_SC : SC gcV := gcG_SC _

theorem gc_Om1_lt_V : Om 1 < gcV := gcG_Om1_lt _

theorem gcV_lt_Om2 (S : InaccSeq.{0}) : gcV < Om (1 + 1) := by
  rw [← gcV_psi S]; exact psi_lt (InR_Om_succ 1) _

theorem gcG_lt_V {α : Ordinal.{0}} (h : α < ε₀) : gcG α < gcV := gcG_lt h

theorem gaW_lt_gcV (S : InaccSeq.{0}) : gaW < gcV := by
  rw [← gcG_omega S]; exact gcG_lt (omega0_lt_epsilon 0)

/-- **Every strongly critical `s` with `Ω₁ < s < gcV` is an atom.** -/
theorem gcSC_cases {s : Ordinal.{0}} (hs : SC s) (h1 : Om 1 < s) (h2 : s < gcV) : s ∈ gcAt := by
  obtain ⟨α, rfl⟩ := enumOrd_surjective gcSet_unbdd (show s ∈ gcSet from ⟨hs, h1⟩)
  exact ⟨α, gcG_lt_iff.1 h2, rfl⟩

theorem gcAt_GxAt : GxAt gcAt := by
  rintro s ⟨α, -, rfl⟩
  exact ⟨gcG_SC α, gcG_Om1_lt α⟩

theorem gcAt_lt_V {s : Ordinal.{0}} (hs : s ∈ gcAt) : s < gcV := by
  obtain ⟨α, hα, rfl⟩ := hs; exact gcG_lt_V hα

theorem gcG_atom {α : Ordinal.{0}} (h : α < ε₀) : gcG α ∈ gcAt := ⟨α, h, rfl⟩

theorem gaAt_sub_gcAt (S : InaccSeq.{0}) : gaAt ⊆ gcAt := by
  rintro s ⟨k, rfl⟩
  exact ⟨k, natCast_lt_epsilon k 0, (gcG_nat S k).symm⟩

theorem gcAt_mem {a b s : Ordinal.{0}} (ha : ε₀ ≤ a) (hs : s ∈ gcAt) : s ∈ S.CSet a b := by
  obtain ⟨α, hα, rfl⟩ := hs
  rw [← gc_psi S α hα.le]
  exact CSet.psi_mem (hα.trans_le ha) (InR_Om_succ 1) (ga_Om2_mem _ _) (gc_cst_mem _ _ α hα)

theorem gc_A_ge (η : Ordinal.{0}) : ε₀ ≤ ConjT.Aη S η := by
  have h : ε₀ ≤ Om ω := epsilon_zero_le_of_omega0_opow_le (Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)).le
  exact h.trans le_self_add

/-! ## The codes -/

variable {Z y : Ordinal.{0}}

/-- **A code over `Z ≤ Ω₁` is below `Γ_{Ω₁+ε₀}`.** -/
theorem gcCl_lt_V (hZ : Z ≤ Om 1) {c : Ordinal.{0}} (hc : GxCl Z gcAt c) : c < gcV := by
  have hSC := gcV_SC
  induction hc with
  | small h => exact (h.trans_le hZ).trans gc_Om1_lt_V
  | om => exact gc_Om1_lt_V
  | atom hs => exact gcAt_lt_V hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

/-- **A code lies in every hull `Cl(a, b)` with `ε₀ ≤ a` and `Z ≤ b`.** -/
theorem gcCl_mem_CSet {a b : Ordinal.{0}} (ha : ε₀ ≤ a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z gcAt x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gcAt_mem ha hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `Γ_{Ω₁+ε₀}` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every
member of `Cl(a, Z)` below `gcV` is a code over `Z`. -/
theorem gcCl_of_CSet {a : Ordinal.{0}} (hZ : 0 < Z) (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < gcV → GxCl Z gcAt x := by
  intro x hx
  have hx' := hx
  have hG2 := (gcV_lt_Om2 S).le
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
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact GxCl.small (hkey _ hx' hlt)
    · have hge : Om 1 ≤ S.psi e.1 π := not_lt.1 fun h' => hπ0 (Low.eq_Om_one_of_psi_lt hπ h')
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact GxCl.atom (gcSC_cases (SC_psi hπ _) (lt_of_le_of_ne hge hne) h)

/-- **Below `Γ_{Ω₁+ω}` a code with the atoms `gcAt` is a code with the atoms `gaAt`.** -/
theorem ga_of_gcCl (S : InaccSeq.{0}) {x : Ordinal.{0}} (hx : GxCl Z gcAt x) : x < gaW → GxCl Z gaAt x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨α, -, rfl⟩ := hs
    rw [← gcG_omega S, gcG_lt_iff] at h
    obtain ⟨k, rfl⟩ := lt_omega0.1 h
    exact GxCl.atom ⟨k, gcG_nat S k⟩
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem gc_of_gaCl (S : InaccSeq.{0}) {x : Ordinal.{0}} (hx : GxCl Z gaAt x) : GxCl Z gcAt x :=
  hx.mono le_rfl (gaAt_sub_gcAt S)

/-- **`Θ_y(c)` with the atoms `gcAt` is `Θ_y(c)` with the atoms `gaAt` for `c ≤ Γ_{Ω₁+ω}`.** -/
theorem gcTh_eq_gaTh (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c ≤ gaW) : gxTh y gcAt c = gxTh y gaAt c :=
  ggOtp_congr c fun _ hx => ⟨fun h => ga_of_gcCl S h (hx.trans_le hc), fun h => gc_of_gaCl S h⟩

/-! ## The readings -/

/-- **The reading is continuous** along any small family: `Θ_y(sup_i f(i)) = sup_i Θ_y(f(i))`. -/
theorem gcTh_iSup {At : Set Ordinal.{0}} {ι : Type*} [Small.{0} ι] (f : ι → Ordinal.{0}) :
    gxTh y At (⨆ i, f i) = ⨆ i, gxTh y At (f i) := by
  classical
  have hbdd : BddAbove (range f) := Ordinal.bddAbove_of_small
  have hbdd' : BddAbove (range fun i => gxTh y At (f i)) := Ordinal.bddAbove_of_small
  refine le_antisymm ?_ (ciSup_le' fun i => gxTh_mono (le_ciSup hbdd i))
  unfold gxTh
  rw [cdOtp_eq]
  refine ciSup_le' fun e => ?_
  split_ifs with he
  · obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.1 e.2
    exact (Order.add_one_le_of_lt (cdOtp_lt_of_mem he hi)).trans (le_ciSup hbdd' i)
  · exact zero_le

/-- **`Θ_y(gcG λ) = sup_{β<λ} Θ_y(gcG β)`** at a limit `λ`. -/
theorem gcTh_limit {At : Set Ordinal.{0}} {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    gxTh y At (gcG l) = ⨆ β : Iio l, gxTh y At (gcG β.1) := by
  rw [gcG_limit hl, gcTh_iSup]

/-- **The reading of every atom is strongly critical, above `y`, below `Ω₁`.** -/
theorem gcTh_G (hy : SC y) (hy1 : y < Om 1) : ∀ α : Ordinal.{0}, α < ε₀ →
    SC (gxTh y gcAt (gcG α)) ∧ y < gxTh y gcAt (gcG α) ∧ gxTh y gcAt (gcG α) < Om 1 := by
  have hAt := gcAt_GxAt
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  have hSC : SC (gxTh y gcAt (gcG α)) := gxTh_SC hy hAt (gcG_SC α) (hy1.trans (gcG_Om1_lt α))
  have hyl : y < gxTh y gcAt (gcG α) := by
    have := gxTh_lt (GxCl.om (Z := y) (At := gcAt)) (gcG_Om1_lt α)
    rwa [gxTh_Om1 hy hy1 hAt] at this
  refine ⟨hSC, hyl, ?_⟩
  have hαΩ : α < Om (1 : Ordinal.{0}) := hα.trans_le gc_eps0_le_Om1
  haveI := gc_countable hαΩ
  rcases eq_or_ne α 0 with rfl | h0
  · have hXS := Lp.lpG_SC hy hy1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hy hy1
    refine (Ld.ldAtom_le hy hy1 hAt hXS hX1 fun t ht htk => ?_).trans_lt hX2
    obtain ⟨β, -, rfl⟩ := ht
    exact absurd (gcG_lt_iff.1 htk) (not_lt.2 zero_le)
  · haveI : Nonempty (Iio α) := ⟨⟨0, pos_iff_ne_zero.2 h0⟩⟩
    set z := ⨆ β : Iio α, gxTh y gcAt (gcG β.1) with hz
    have hbdd : BddAbove (range fun β : Iio α => gxTh y gcAt (gcG β.1)) := Ordinal.bddAbove_of_small
    have hzS : SC z := gc_SC_iSup fun β => (IH β.1 β.2 (β.2.trans hα)).1
    have hz1 : z < Om 1 := by
      have := Ordinal.iSup_lt_omega_one (f := fun β : Iio α => gxTh y gcAt (gcG β.1)) fun β => by
        have h := (IH β.1 β.2 (β.2.trans hα)).2.2
        rwa [← ph_Om1_eq] at h
      rwa [← ph_Om1_eq]
    have hyz : y < z := (IH 0 (pos_iff_ne_zero.2 h0) ((pos_iff_ne_zero.2 h0).trans hα)).2.1.trans_le
      (le_ciSup hbdd ⟨0, pos_iff_ne_zero.2 h0⟩)
    have hXS := Lp.lpG_SC hzS hz1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts hzS hz1
    refine (Ld.ldAtom_le hy hy1 hAt hXS (hyz.trans hX1) fun t ht htk => ?_).trans_lt hX2
    obtain ⟨β, -, rfl⟩ := ht
    have hβ := gcG_lt_iff.1 htk
    exact (le_ciSup hbdd ⟨β, hβ⟩).trans_lt hX1

/-- **The reading of every atom is strongly critical, above `y`, below `Ω₁`.** -/
theorem gcTh_At (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ gcAt) :
    SC (gxTh y gcAt s) ∧ y < gxTh y gcAt s ∧ gxTh y gcAt s < Om 1 := by
  obtain ⟨α, hα, rfl⟩ := hs
  exact gcTh_G hy hy1 α hα

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem gcTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y gcAt c) :
    gxTh y gcAt c < Om 1 := by
  have hAt := gcAt_GxAt
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (gcTh_At hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Terms for the codes -/

/-- **Terms for the codes below `E`** (atoms `gcAt`): for every code `c < E` over `Z` some term of `X` has the value
`Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GcPoly (X : XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z gcAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y gcAt c

/-- **Reduction to strongly critical `Z`.** -/
theorem gcPoly_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → ∀ c, GxCl Z gcAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
      X.CB s y ∧ X.val s y = gxTh y gcAt c) : GcPoly X E := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 c (hc.mono h3 Subset.rfl) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

/-- **`GaPoly X E` with `E ≤ Γ_{Ω₁+ω}` gives `GcPoly X E`.** -/
theorem gcPoly_of_ga (S : InaccSeq.{0}) {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ gaW) (h : GaPoly X E) :
    GcPoly X E := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := h Z c (ga_of_gcCl S hc (hcE.trans_le hE)) hcE
  refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
  rw [(hs y hy hy1 hZy).2, gcTh_eq_gaTh S (hcE.trans_le hE).le]

end Googology.Trans.PoR.InaccPsi.R2.Gc
