import Googology.Trans.PoR.InaccPsi.R2.MxAtB

/-!
# The layers `K_j` and the atoms `ψ_{Ω₂}(α)` with `α` a code of the previous layer, and their readings

`ψ = S.psi`, `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(K_j)` (`mxKs`), `mxAtL S ρ j` the atoms of layer `j` (none for `j = 0`;
`ψ_{Ω₂}(α)` for the codes `α < K_j` of layer `j` for `j + 1`), `GxCl ρ (mxAtL S ρ j)` the codes of layer `j`.
`H_λ = Cl(A_{η_λ}, ρ_λ)`, `Θ_λ(m) = otp(H_λ ∩ m)`.  An argument `A` is own when `A ∈ Cl(A, ψ_{Ω₁}(A))`.

* `mxKs_lt_succ`, `mxKs_lt_Om2`, `mxKs_le_th` (`K_j < K_{j+1} < Ω₂`, `K_j ≤ θ`), `mxPsi2_gt` (**`β < ψ_{Ω₂}(β)` for
  `β < K_j`**, so every such `β` is own for `ψ_{Ω₂}`), `mxPsi2_ltL`, `mxPsi2_lt_iffL` (`ψ_{Ω₂}` is strictly
  increasing on `[0, K_j)`);
* `mxAtL_GxAt`, `mxAtL_mono`, `mxAtL_lt`, `mxAtL_low` (**the codes of layer `j + 1` below `K_j` are those of layer
  `j`**), `mxThL_congr`;
* `mxHullL_iff` (**at every named restart the hull below `K_j` is the set of the codes of layer `j`**),
  `mxThetaL` (**`Θ_λ(m) = gxTh ρ_λ (mxAtL ρ_λ j) m` for `m ≤ K_j`**);
* `mxThL_atom` (**`Θ(ψ_{Ω₂}(α)) = ψ_{Ω₁}(A + 1 + Θ(α))`** for a code `α < K_j` of layer `j`, `ρ = ψ_{Ω₁}(A)`, `A`
  own: both sides are the least strongly critical ordinal above `ρ` and above the values at the codes `β < α`).

No new axiom.  New definitions: `mxKs`, `mxAtL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-- `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(K_j)`. -/
noncomputable def mxKs (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (mxKs S j) (Om (1 + 1))

/-- The atoms of layer `j`: none for `j = 0`; `ψ_{Ω₂}(α)` for the codes `α < K_j` of layer `j` for `j + 1`. -/
def mxAtL (S : InaccSeq.{0}) (ρ : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => ∅
  | j + 1 => {s | ∃ α, GxCl ρ (mxAtL S ρ j) α ∧ α < mxKs S j ∧ s = S.psi α (Om (1 + 1))}

theorem mxKs_zero : mxKs S 0 = Om 1 := rfl

theorem mxKs_succ (j : ℕ) : mxKs S (j + 1) = S.psi (mxKs S j) (Om (1 + 1)) := rfl

theorem mxKs_lt_Om2 : ∀ j, mxKs S j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem mxKs_SC : ∀ j, SC (mxKs S j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem mxKs_lt_succ : ∀ j, mxKs S j < mxKs S (j + 1)
  | 0 => (psiS_bounds (S := S) (Om 1) 1).1
  | j + 1 => by
    have IH := mxKs_lt_succ j
    have hle : mxKs S (j + 1) ≤ mxKs S (j + 2) := (psi_mono (S := S) (InR_Om_succ 1) IH.le).1
    exact psi_lt_psi_of_mem (InR_Om_succ 1) IH (CSet.of_lt (IH.trans_le hle))

theorem mxKs_mono {j j' : ℕ} (h : j ≤ j') : mxKs S j ≤ mxKs S j' :=
  (strictMono_nat_of_lt_succ (fun k => mxKs_lt_succ (S := S) k)).monotone h

theorem mxOm1_le_Ks (j : ℕ) : Om (1 : Ordinal.{0}) ≤ mxKs S j := mxKs_mono (S := S) (Nat.zero_le j)

/-- `K_j ≤ θ`. -/
theorem mxKs_le_th : ∀ j, mxKs S j ≤ ConjT.th S
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1)
      ((mxKs_lt_Om2 j).le.trans (Om_le_Om.2 (by
        rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le)))).1

/-- **`β < ψ_{Ω₂}(β)` for `β < K_j`.** -/
theorem mxPsi2_gt : ∀ j β, β < mxKs S j → β < S.psi β (Om (1 + 1))
  | 0, β, h => h.trans (psiS_bounds (S := S) β 1).1
  | j + 1, β, h => by
    rcases lt_or_ge β (mxKs S j) with h' | h'
    · exact mxPsi2_gt j β h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) h').1

theorem mxPsi2_ltL {j : ℕ} {α β : Ordinal.{0}} (h : α < β) (hβ : β < mxKs S j) :
    S.psi α (Om (1 + 1)) < S.psi β (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) h (CSet.of_lt (h.trans (mxPsi2_gt j β hβ)))

theorem mxPsi2_lt_iffL {j : ℕ} {α β : Ordinal.{0}} (hα : α < mxKs S j) (hβ : β < mxKs S j) :
    S.psi α (Om (1 + 1)) < S.psi β (Om (1 + 1)) ↔ α < β := by
  refine ⟨fun h => ?_, fun h => mxPsi2_ltL h hβ⟩
  by_contra h'
  push Not at h'
  rcases h'.lt_or_eq with h'' | rfl
  · exact absurd (mxPsi2_ltL h'' hα) (not_lt.2 h.le)
  · exact lt_irrefl _ h

/-! ## The atoms of the layers -/

theorem mxAtL_GxAt (ρ : Ordinal.{0}) : ∀ j, GxAt (mxAtL S ρ j)
  | 0 => fun _ h => absurd h (Set.notMem_empty _)
  | _ + 1 => by
    rintro s ⟨α, -, -, rfl⟩
    exact ⟨SC_psi (InR_Om_succ 1) α, (psiS_bounds α 1).1⟩

theorem mxAtL_mono (ρ : Ordinal.{0}) : ∀ j, mxAtL S ρ j ⊆ mxAtL S ρ (j + 1)
  | 0 => Set.empty_subset _
  | j + 1 => by
    rintro s ⟨α, hα, hαK, rfl⟩
    exact ⟨α, hα.mono le_rfl (mxAtL_mono ρ j), hαK.trans (mxKs_lt_succ j), rfl⟩

theorem mxAtL_lt (ρ : Ordinal.{0}) : ∀ j, ∀ s ∈ mxAtL S ρ j, s < mxKs S j
  | 0 => fun _ h => absurd h (Set.notMem_empty _)
  | j + 1 => by
    rintro s ⟨α, -, hαK, rfl⟩
    exact mxPsi2_ltL hαK (mxKs_lt_succ j)

/-- Restriction of the atoms below a bound. -/
theorem mxGx_restrict {Z K : Ordinal.{0}} {At At' : Set Ordinal.{0}} (h : ∀ s ∈ At', s < K → s ∈ At) :
    ∀ x, GxCl Z At' x → x < K → GxCl Z At x := by
  intro x hx
  induction hx with
  | small h' => exact fun _ => GxCl.small h'
  | om => exact fun _ => GxCl.om
  | atom hs => exact fun hK => GxCl.atom (h _ hs hK)
  | @add x y _ _ ihx ihy =>
    exact fun hK => GxCl.add (ihx (lt_of_le_of_lt le_self_add hK)) (ihy (lt_of_le_of_lt le_add_self hK))
  | @phi x y _ _ ihx ihy =>
    exact fun hK => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) hK))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) hK))

/-- **The codes of layer `j + 1` below `K_j` are those of layer `j`.** -/
theorem mxAtL_low (ρ : Ordinal.{0}) : ∀ j, ∀ x, GxCl ρ (mxAtL S ρ (j + 1)) x → x < mxKs S j →
    GxCl ρ (mxAtL S ρ j) x
  | 0 => mxGx_restrict fun s hs hK => absurd hK (not_lt.2 (mxAtL_GxAt ρ 1 s hs).2.le)
  | j + 1 => mxGx_restrict fun s hs hK => by
    obtain ⟨α, hα, hαK, rfl⟩ := hs
    have hαj : α < mxKs S j := by
      have h1 : S.psi α (Om (1 + 1)) < S.psi (mxKs S j) (Om (1 + 1)) := hK
      exact (mxPsi2_lt_iffL (j := j + 1) hαK (mxKs_lt_succ j)).1 h1
    exact ⟨α, mxAtL_low ρ j α hα hαj, hαj, rfl⟩

theorem mxThL_congr (ρ : Ordinal.{0}) (j : ℕ) {m : Ordinal.{0}} (hm : m ≤ mxKs S j) :
    gxTh ρ (mxAtL S ρ j) m = gxTh ρ (mxAtL S ρ (j + 1)) m :=
  ggOtp_congr m fun x hx => ⟨fun h => h.mono le_rfl (mxAtL_mono ρ j),
    fun h => mxAtL_low ρ j x h (hx.trans_le hm)⟩

/-! ## The hull below `K_j` -/

/-- The codes of every layer are in the hull. -/
theorem mxGxL_hull {l : Ordinal.{0}} :
    ∀ j x, GxCl (upsilon l) (mxAtL S (upsilon l) j) x → x ∈ cdHull S l := by
  have hWA : Om ω ≤ ConjT.Aη S (cdEta S l) := le_self_add
  intro j
  induction j with
  | zero =>
    intro x hx
    induction hx with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs => exact absurd hs (Set.notMem_empty _)
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | succ j IH =>
    intro x hx
    induction hx with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs =>
      obtain ⟨α, hα, hαK, rfl⟩ := hs
      have hα2 : α < Om ω := (hαK.trans (mxKs_lt_Om2 j)).trans (Om_lt_Om.2 (by
        rw [one_add_one_eq_two]; exact natCast_lt_omega0 2))
      exact CSet.psi_mem (hα2.trans_le hWA) (InR_Om_succ 1) (mxOm2_mem _ _) (IH α hα)
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **At a named restart the hull below `K_j` is the set of the codes of layer `j`.** -/
theorem mxHullL_iff {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ j x, x < mxKs S j → (x ∈ cdHull S l ↔ GxCl (upsilon l) (mxAtL S (upsilon l) j) x) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA
  have hρ : S.psi A (Om 1) = upsilon l := hpv
  have hρ0 : 0 < upsilon l := mvUps_pos hl
  have key : ∀ y ∈ S.CSet A (upsilon l), y < Om 1 → y < upsilon l := fun y hy hy1 => by
    rw [← hρ] at hy ⊢; exact lt_psi_of_mem Low.InR_Om_one hy hy1
  intro j
  induction j with
  | zero =>
    intro x hxK
    refine ⟨fun hx => GxCl.small (key x hx hxK), fun hx => mxGxL_hull 0 x hx⟩
  | succ j IH =>
    intro x hxK
    refine ⟨fun hx => ?_, fun hx => mxGxL_hull (j + 1) x hx⟩
    have hK2 := mxKs_lt_Om2 (S := S) (j + 1)
    unfold cdHull at hx
    rw [← hA] at hx
    revert hxK
    have hx' := hx
    induction hx with
    | small h => exact fun _ => GxCl.small h
    | zero => exact fun _ => GxCl.zero hρ0
    | inacc n =>
      exact fun h => absurd ((h.trans hK2).trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW =>
      exact fun h => absurd ((h.trans hK2).trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
    | @phi x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
        (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x hx1 _ =>
      intro h
      have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans hK2)
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hρ0
      · rw [h1]; exact GxCl.om
    | @coll π e hπ hπ1 he1 _ _ =>
      intro h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans (h.trans hK2)) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add] at hx' ⊢
        exact GxCl.small (key _ hx' (psi_lt Low.InR_Om_one _))
      rcases eq_or_ne s 1 with rfl | hs1
      · rcases lt_or_ge e.1 (mxKs S j) with he | he
        · exact GxCl.atom ⟨e.1, (IH e.1 he).1 he1, he, rfl⟩
        · exact absurd ((psi_mono (S := S) (InR_Om_succ 1) he).1) (not_le.2 h)
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans (h.trans hK2)) (lt_irrefl _)

/-- **`Θ_λ(m) = gxTh ρ_λ (mxAtL ρ_λ j) m`** for `m ≤ K_j` at a named restart. -/
theorem mxThetaL {l ηx m : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (j : ℕ)
    (hm : m ≤ mxKs S j) : cdTheta S l m = gxTh (upsilon l) (mxAtL S (upsilon l) j) m :=
  ggOtp_congr m fun x hx => mxHullL_iff hl hX j x (hx.trans_le hm)

/-! ## The readings of the atoms of every layer -/

/-- **`Θ(ψ_{Ω₂}(α)) = ψ_{Ω₁}(A + 1 + Θ(α))`** for a code `α < K_j` of layer `j`, `ρ = ψ_{Ω₁}(A)`, `A` own. -/
theorem mxThL_atom {ρ A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = ρ)
    (j : ℕ) : ∀ α, GxCl ρ (mxAtL S ρ j) α → α < mxKs S j →
      gxTh ρ (mxAtL S ρ (j + 1)) (S.psi α (Om (1 + 1))) =
        S.psi (A + 1 + gxTh ρ (mxAtL S ρ (j + 1)) α) (Om 1) := by
  have hρSC : SC ρ := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : ρ < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  set At := mxAtL S ρ (j + 1) with hAt_def
  have hAt : GxAt At := mxAtL_GxAt ρ (j + 1)
  have hρb : ∀ γ, ρ < S.psi (A + 1 + γ) (Om 1) := by
    intro γ
    rw [← hρ]
    refine psi_lt_psi_of_mem Low.InR_Om_one ((lt_add_one A).trans_le le_self_add) ?_
    exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA
  have hmemA : ∀ γ d, A + 1 + γ ≤ d → γ < S.psi d (Om 1) → A + 1 + γ ∈ S.CSet d (S.psi d (Om 1)) := by
    intro γ d hd hγ
    have hAd : A ≤ d := le_self_add.trans (le_self_add.trans hd)
    exact CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hAd).2 hA) (CSet.one_mem _ _))
      (CSet.of_lt hγ)
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα hαK
  have hα' : GxCl ρ At α := hα.mono le_rfl (mxAtL_mono ρ j)
  have hαψ : α < S.psi α (Om (1 + 1)) := mxPsi2_gt j α hαK
  set T := gxTh ρ At (S.psi α (Om (1 + 1))) with hT
  set b := S.psi (A + 1 + gxTh ρ At α) (Om 1) with hb
  have hTSC : SC T := gxTh_SC hρSC hAt (SC_psi (InR_Om_succ 1) α)
    (hρ1.trans (psiS_bounds (S := S) α 1).1)
  have hρT : ρ < T := by
    have := gxTh_lt (Z := ρ) (At := At) GxCl.om (psiS_bounds (S := S) α 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at this
  have hβT : ∀ β, GxCl ρ (mxAtL S ρ j) β → β < α → S.psi (A + 1 + gxTh ρ At β) (Om 1) < T := by
    intro β hβ hβα
    rw [← IH β hβα hβ (hβα.trans hαK)]
    exact gxTh_lt (GxCl.atom ⟨β, hβ, hβα.trans hαK, rfl⟩) (mxPsi2_ltL hβα hαK)
  apply le_antisymm
  · -- `T ≤ b`
    have hbd : ∀ c, GxCl ρ At c → c < S.psi α (Om (1 + 1)) → gxTh ρ At c < b := by
      refine mxGx_bound hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρb _) ?_
      rintro s ⟨β, hβ, hβK, rfl⟩ hs
      have hβα : β < α := (mxPsi2_lt_iffL hβK hαK).1 hs
      have hβ' : GxCl ρ At β := hβ.mono le_rfl (mxAtL_mono ρ j)
      have hΘβα : gxTh ρ At β < gxTh ρ At α := gxTh_lt hβ' hβα
      have hle : S.psi (A + 1 + gxTh ρ At β) (Om 1) ≤ b :=
        (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left _).2 hΘβα.le)).1
      have hΘβb : gxTh ρ At β < b := by
        refine lt_of_lt_of_le ?_ hle
        rw [← IH β hβα hβ hβK]
        exact gxTh_lt hβ' (mxPsi2_gt j β hβK)
      rw [IH β hβα hβ hβK]
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left _).2 hΘβα)
        (hmemA _ _ ((add_le_add_iff_left _).2 hΘβα.le) hΘβb)
    rw [hT]
    unfold gxTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · exact Order.add_one_le_of_lt (hbd c.1 hc c.2)
    · exact zero_le
  · -- `b ≤ T`
    refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
    intro x hx
    induction hx with
    | @small x hxb => exact fun _ => hxb
    | zero => exact fun _ => hTSC.1
    | inacc n => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_I S n).le)
    | inaccW => exact fun h => absurd h (not_lt.2 (gg_Om1_lt_Iw S).le)
    | @add x y _ _ ihx ihy =>
      intro h
      exact hTSC.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
    | @phi x y _ _ ihx ihy =>
      intro h
      exact hTSC.2 x (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) y
        (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x _ _ =>
      intro h
      rw [mxOm_lt_one h, Om_zero]
      exact hTSC.1
    | @coll π e hπ _ _ _ _ =>
      intro h
      have hπ1 : π = Om 1 := by
        by_contra hne
        exact absurd h (not_lt.2 (mxOm1_le_psi hπ hne))
      subst hπ1
      rcases le_or_gt e.1 A with heA | heA
      · exact lt_of_le_of_lt (hρ ▸ (psi_mono (S := S) Low.InR_Om_one heA).1) hρT
      · obtain ⟨d, hd⟩ := exists_add_of_le heA.le
        have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hd; exact absurd hd heA.ne'
        have hd1 : d < 1 + gxTh ρ At α := by
          have := e.2; rw [hd, add_assoc] at this; exact (add_lt_add_iff_left A).1 this
        have hdec : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hd0)
        have hγα : d - 1 < gxTh ρ At α := by
          rw [← hdec] at hd1; exact (add_lt_add_iff_left 1).1 hd1
        obtain ⟨β, hβ, hβα, hβe⟩ := gxTh_onto hγα
        have hβj : GxCl ρ (mxAtL S ρ j) β := mxAtL_low ρ j β hβ (hβα.trans hαK)
        have he : e.1 = A + 1 + gxTh ρ At β := by rw [hd, add_assoc, hβe, hdec]
        show S.psi e.1 (Om 1) < T
        rw [he]
        exact hβT β hβj hβα

end Googology.Trans.PoR.InaccPsi.R2.Mx
