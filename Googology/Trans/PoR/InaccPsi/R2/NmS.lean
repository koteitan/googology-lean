import Googology.Trans.PoR.InaccPsi.R2.NmL
import Googology.Trans.PoR.InaccPsi.R2.OffG2

/-!
# The segments of `ψ_{Ω₁}(Ω_ω + θ·η)` along multiples of `Ω₁^γ`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Pv`); `η` is good when
`η ∈ Cl(A_η + 1, P(η))` (`R2.Bt.Good`); `V_γ = veblenWith υ γ` (`R2.VG`).  For a normal `F`,
`nxt F x` is the least value of `F` above `x`.  `Zu η₀ u` is the least `β` with `P(η₀ + u·β) ≤ β`.

* `cont_le` (**Lemma CONT**): `P(η₀ + X) ≤ B` for a limit `X` when `P(η₀ + c) ≤ B` for every `c < X`;
* `aseg` (**the segment lemma**): if every step `η₀ + u·β ↦ η₀ + u·(β+1)` is a step of `F`, then
  `P(η₀ + u·β) = F(c₀ + β)` along the whole segment;
* `start_all` (**Theorem START**): for every `γ`, a good `η₁` that is a multiple of `Ω₁^γ`, with
  `δ < nxt V_δ (P(η₁))` for every `δ < γ`: `P(η₁ + Ω₁^γ) = nxt V_γ (P(η₁))`;
* `seg_all` (**Theorem SEG at level `γ`**): for a good `η₀` that is a multiple of `Ω₁^γ`, with
  `γ < P(η₀) = V_γ(c₀)`: `P(η₀ + Ω₁^γ·β) = V_γ(c₀ + β)` for every `β ≤ Zu η₀ Ω₁^γ`;
* `zu_eq_nxt`: `Zu (η₁ + Ω₁^γ) Ω₁^γ = nxt V_{γ+1} (P(η₁))` under the hypotheses of Theorem START at `γ+1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)`. -/
noncomputable abbrev Pv (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (ConjT.Aη S η) (Om 1)

/-- The least value of `F` above `x`. -/
noncomputable def nxt (F : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} :=
  F (sInf {c | x < F c})

/-- `Zu η₀ u`: the least `β` with `P(η₀ + u·β) ≤ β`. -/
noncomputable def Zu (S : InaccSeq.{0}) (η0 u : Ordinal.{0}) : Ordinal.{0} :=
  sInf {β | Pv S (η0 + u * β) ≤ β}

variable {S : InaccSeq.{0}}

/-! ## `P` -/

theorem Pv_mono {η η' : Ordinal.{0}} (h : η ≤ η') : Pv S η ≤ Pv S η' := psi_A_mono S h

theorem Pv_SC (S : InaccSeq.{0}) (η : Ordinal.{0}) : SC (Pv S η) := SC_psi Low.InR_Om_one _

theorem Pv_lt_Om1 (S : InaccSeq.{0}) (η : Ordinal.{0}) : Pv S η < Om 1 := psi_lt Low.InR_Om_one _

theorem Pv_zero (S : InaccSeq.{0}) : Pv S 0 = upsilon 1 := by
  have h := ups_eq_le_etaS S (zero_le : (0 : Ordinal.{0}) ≤ etaS S)
  rw [add_zero] at h; exact h.symm

/-- At a good `η`: `P(η) < P(η + 1)`. -/
theorem Pv_lt_succ {η : Ordinal.{0}} (h : Bt.Good S η) : Pv S η < Pv S (η + 1) := by
  have := psi_lt_succ_of_HA (HA_of_good S h)
  rwa [ConjT.A_succ] at this

/-- **Lemma CONT**: `P(η₀ + X) ≤ B` for a limit `X` when `P(η₀ + c) ≤ B` for every `c < X`. -/
theorem cont_le {η0 X B : Ordinal.{0}} (hX : IsSuccLimit X) (h : ∀ c < X, Pv S (η0 + c) ≤ B) :
    Pv S (η0 + X) ≤ B := by
  have hlim : IsSuccLimit (ConjT.Aη S (η0 + X)) := by
    rw [A_add]; exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos hX)
  refine psi_limit_le S hlim fun e he => ?_
  rcases lt_or_ge e (ConjT.Aη S η0) with h1 | h1
  · have := h 0 hX.bot_lt
    rw [add_zero] at this
    exact (psi_mono Low.InR_Om_one h1.le).1.trans this
  · obtain ⟨d, rfl⟩ := exists_add_of_le h1
    rw [A_add] at he
    have hd : d < ConjT.th S * X := (add_lt_add_iff_left _).1 he
    obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit hX).1 hd
    have hle : ConjT.Aη S η0 + d ≤ ConjT.Aη S (η0 + c) := by rw [A_add]; gcongr
    exact (psi_mono Low.InR_Om_one hle).1.trans (h c hc)

/-! ## `Zu` -/

theorem Zu_mem (S : InaccSeq.{0}) (η0 u : Ordinal.{0}) : Pv S (η0 + u * Zu S η0 u) ≤ Zu S η0 u :=
  csInf_mem (s := {β | Pv S (η0 + u * β) ≤ β}) ⟨Om 1, (Pv_lt_Om1 S _).le⟩

theorem lt_Pv_of_lt_Zu {η0 u β : Ordinal.{0}} (h : β < Zu S η0 u) : β < Pv S (η0 + u * β) := by
  by_contra hle
  rw [not_lt] at hle
  exact absurd (csInf_le' (s := {β | Pv S (η0 + u * β) ≤ β}) hle) (not_le.2 h)

theorem Zu_fix (S : InaccSeq.{0}) (η0 u : Ordinal.{0}) : Pv S (η0 + u * Zu S η0 u) = Zu S η0 u := by
  refine le_antisymm (Zu_mem S η0 u) ?_
  by_contra hlt
  rw [not_le] at hlt
  have h1 := lt_Pv_of_lt_Zu hlt
  have h2 := Pv_mono (S := S) (show η0 + u * Pv S (η0 + u * Zu S η0 u) ≤ η0 + u * Zu S η0 u by
    gcongr)
  exact absurd (h1.trans_le h2) (lt_irrefl _)

theorem Zu_SC (S : InaccSeq.{0}) (η0 u : Ordinal.{0}) : SC (Zu S η0 u) := by
  rw [← Zu_fix]; exact Pv_SC S _

theorem Zu_lt_Om1 (S : InaccSeq.{0}) (η0 u : Ordinal.{0}) : Zu S η0 u < Om 1 := by
  rw [← Zu_fix]; exact Pv_lt_Om1 S _

/-! ## The least value above -/

section nxt

variable {F : Ordinal.{0} → Ordinal.{0}}

theorem nxt_spec (hF : IsNormal F) (hF0 : F 0 = 0) (x : Ordinal.{0}) :
    ∃ c, F c ≤ x ∧ x < F (c + 1) ∧ nxt F x = F (c + 1) := by
  obtain ⟨c, h1, h2⟩ := hF.exists_map_le_lt_map_succ (x := x) (by
    show F 0 ≤ x; rw [hF0]; exact zero_le)
  rw [Order.succ_eq_add_one] at h2
  refine ⟨c, h1, h2, ?_⟩
  unfold nxt
  congr 1
  refine le_antisymm (csInf_le' h2) (le_csInf ⟨_, h2⟩ fun c' hc' => ?_)
  exact Order.add_one_le_of_lt (hF.strictMono.lt_iff_lt.1 (h1.trans_lt hc'))

theorem lt_nxt (hF : IsNormal F) (hF0 : F 0 = 0) (x : Ordinal.{0}) : x < nxt F x := by
  obtain ⟨c, -, h2, h3⟩ := nxt_spec hF hF0 x
  rw [h3]; exact h2

theorem nxt_mem (F : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}) : nxt F x ∈ range F :=
  ⟨_, rfl⟩

theorem nxt_le (hF : IsNormal F) (hF0 : F 0 = 0) {x y : Ordinal.{0}} (hy : y ∈ range F)
    (hxy : x < y) : nxt F x ≤ y := by
  obtain ⟨d, rfl⟩ := hy
  obtain ⟨c, h1, -, h2⟩ := nxt_spec hF hF0 x
  rw [h2]
  exact hF.strictMono.monotone (Order.add_one_le_of_lt (hF.strictMono.lt_iff_lt.1 (h1.trans_lt hxy)))

theorem nxt_apply (hF : IsNormal F) (hF0 : F 0 = 0) (c : Ordinal.{0}) : nxt F (F c) = F (c + 1) := by
  obtain ⟨c', h1, h3, h2⟩ := nxt_spec hF hF0 (F c)
  rw [h2]
  have hc : c' ≤ c := hF.strictMono.le_iff_le.1 h1
  rcases eq_or_lt_of_le hc with rfl | hlt
  · rfl
  · exfalso
    exact absurd (hF.strictMono.lt_iff_lt.1 h3) (not_lt.2 (Order.add_one_le_of_lt hlt))

end nxt

/-! ## The fixed points of `V_γ` -/

theorem VG0 : VG 0 0 = 0 := VG_at_zero 0

/-- A nonzero value of `V_γ` is an `ε`-number. -/
theorem VG_inE (g : Ordinal.{0}) {c : Ordinal.{0}} (hc : c ≠ 0) : ω ^ VG g c = VG g c := by
  obtain ⟨i, hi⟩ := veblenWith_mem_range (f := upsilon) (o := g) (a := c) upsilon_normal
  have hi0 : 0 < i := by
    rcases eq_or_ne i 0 with rfl | h
    · exfalso
      rw [upsilon_zero] at hi
      have := VG_pos (g := g) (pos_iff_ne_zero.2 hc)
      exact (ne_of_gt this) (by rw [VG]; exact hi.symm)
    · exact pos_iff_ne_zero.2 h
  have h := upsPt_inE (upsPt_upsilon hi0)
  rw [VG, ← hi]; exact h

theorem VG_isSuccLimit (g : Ordinal.{0}) {c : Ordinal.{0}} (hc : c ≠ 0) : IsSuccLimit (VG g c) := by
  have he := VG_inE g hc
  refine eps_isSuccLimit he ?_
  by_contra h1
  rw [not_lt] at h1
  rcases Order.le_one_iff.1 h1 with h | h
  · exact absurd h (VG_pos (pos_iff_ne_zero.2 hc)).ne'
  · rw [h, opow_one] at he; exact absurd he (ne_of_gt one_lt_omega0)

theorem VG_principal (g : Ordinal.{0}) (c : Ordinal.{0}) : IsPrincipal (· + ·) (VG g c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [VG_at_zero]; exact isPrincipal_add_of_le_one zero_le_one
  · rw [← VG_inE g hc]; exact isPrincipal_add_omega0_opow _

/-- `range V_γ ⊆ range V_δ` for `δ ≤ γ`. -/
theorem range_VG_anti {δ γ y : Ordinal.{0}} (h : δ ≤ γ) (hy : y ∈ range (VG γ)) : y ∈ range (VG δ) := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hy
  · obtain ⟨c, rfl⟩ := hy
    exact ⟨VG γ c, VG_VG hlt c⟩

/-- The least value of `V_γ` above `x` is not a fixed point of `V_γ`. -/
theorem nxt_not_fix (g x : Ordinal.{0}) : VG g (nxt (VG g) x) ≠ nxt (VG g) x := by
  obtain ⟨c, -, -, h2⟩ := nxt_spec (VG_normal g) (VG_at_zero g) x
  intro hfix
  rw [h2] at hfix
  have e := (VG_strictMono g).injective hfix
  have hc0 : c + 1 ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one c))
  have hlim := VG_isSuccLimit g hc0
  rw [e] at hlim
  exact lt_irrefl _ (hlim.add_one_lt (lt_add_one c))

/-- `range V_{γ+1}` is the set of fixed points of `V_γ`. -/
theorem mem_range_VG_succ {g y : Ordinal.{0}} : y ∈ range (VG (g + 1)) ↔ VG g y = y := by
  rw [mem_range_VG (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one g)))]
  constructor
  · intro h; exact h g (lt_add_one g)
  · intro h b hb
    rcases eq_or_lt_of_le (Order.lt_add_one_iff.1 hb) with rfl | hlt
    · exact h
    · rw [← h]; exact VG_VG hlt y

/-! ## Membership in the hull -/

theorem mem_opow_mul {a b e β : Ordinal.{0}} (he : e ∈ S.CSet a b) (hβ : β < b) :
    ω ^ e * β ∈ S.CSet a b := by
  obtain ⟨L, hL1, -, hL3⟩ := exists_prin_list β
  rw [← hL3, ← foldr_map_mul]
  refine foldr_mem _ fun l hl => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hp, h0, hle⟩ := hL1 y hy
  obtain ⟨c, rfl⟩ := prin_eq_opow hp h0
  rw [← opow_add, ← veblen_zero_apply]
  refine CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem he (CSet.of_lt ?_))
  exact lt_of_le_of_lt ((Ordinal.right_le_opow c one_lt_omega0).trans hle) hβ

theorem mem_Om1_mul {a b γ : Ordinal.{0}} (hγ : γ < b) : Om 1 * γ ∈ S.CSet a b := by
  have := mem_opow_mul (S := S) (CSet.Om_mem (CSet.one_mem a b)) hγ
  rwa [Om1_opow] at this

theorem mem_Om1_pow {a b γ : Ordinal.{0}} (hγ : γ < b) : Om (1 : Ordinal.{0}) ^ γ ∈ S.CSet a b := by
  rw [Om1_pow, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (mem_Om1_mul hγ)

theorem mem_Om1_pow_mul {a b γ β : Ordinal.{0}} (hγ : γ < b) (hβ : β < b) :
    Om (1 : Ordinal.{0}) ^ γ * β ∈ S.CSet a b := by
  rw [Om1_pow]; exact mem_opow_mul (mem_Om1_mul hγ) hβ

theorem mem_W_mul {a b β : Ordinal.{0}} (hβ : β < b) :
    Om (1 : Ordinal.{0}) ^ Om (1 : Ordinal.{0}) * β ∈ S.CSet a b := by
  have h1 : Om (1 : Ordinal.{0}) ∈ S.CSet a b := CSet.Om_mem (CSet.one_mem a b)
  have h2 : Om (1 : Ordinal.{0}) * Om 1 ∈ S.CSet a b := by
    rw [← Om1_opow, ← opow_add, ← veblen_zero_apply]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem h1 h1)
  rw [Om1_pow]; exact mem_opow_mul h2 hβ

theorem good_zero (S : InaccSeq.{0}) : Bt.Good S 0 := CSet.zero_mem _ _

/-- `η + δ` is good when `η` is good and `δ` is in the hull of `η + δ`. -/
theorem good_add {η δ : Ordinal.{0}} (h : Bt.Good S η)
    (hδ : δ ∈ S.CSet (ConjT.Aη S (η + δ) + 1) (Pv S (η + δ))) : Bt.Good S (η + δ) := by
  refine CSet.add_mem ?_ hδ
  exact CSet_mono (add_le_add_left (ConjT.A_mono S le_self_add) 1) (Pv_mono le_self_add) h

/-! ## The segment lemma -/

/-- **The segment lemma.** -/
theorem aseg {F : Ordinal.{0} → Ordinal.{0}} (hF : IsNormal F) {u η0 c0 B : Ordinal.{0}}
    (hu : 0 < u) (h0 : Pv S η0 = F c0)
    (hstep : ∀ β' < B, Pv S (η0 + u * β') = F (c0 + β') →
      Pv S (η0 + u * (β' + 1)) = F (c0 + β' + 1)) :
    ∀ β ≤ B, Pv S (η0 + u * β) = F (c0 + β) := by
  intro β
  induction β using Ordinal.limitRecOn with
  | zero => intro _; simpa using h0
  | add_one β ih =>
    intro hb
    have hb' : β < B := (lt_add_one β).trans_le hb
    rw [← add_assoc]; exact hstep β hb' (ih hb'.le)
  | limit l hl ih =>
    intro hb
    apply le_antisymm
    · refine cont_le (isSuccLimit_mul_right hu hl) fun c hc => ?_
      obtain ⟨β', hβ', hcβ⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hc
      calc Pv S (η0 + c) ≤ Pv S (η0 + u * β') := Pv_mono (by gcongr)
        _ = F (c0 + β') := ih β' hβ' (hβ'.le.trans hb)
        _ ≤ F (c0 + l) := hF.strictMono.monotone (by gcongr)
    · refine (hF.le_iff_forall_le (isSuccLimit_add c0 hl)).2 fun b hb' => ?_
      rcases lt_or_ge b c0 with h1 | h1
      · calc F b ≤ F c0 := hF.strictMono.monotone h1.le
          _ = Pv S η0 := h0.symm
          _ ≤ _ := Pv_mono le_self_add
      · obtain ⟨d, rfl⟩ := exists_add_of_le h1
        have hd : d < l := (add_lt_add_iff_left _).1 hb'
        rw [← ih d hd (hd.le.trans hb)]
        exact Pv_mono (by gcongr)

/-! ## Theorem START and Theorem SEG -/

/-- The statement of Theorem START at level `γ`. -/
def STARTst (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ η1, Bt.Good S η1 → Om (1 : Ordinal.{0}) ^ γ ∣ η1 → (∀ δ < γ, δ < nxt (VG δ) (Pv S η1)) →
    Pv S (η1 + Om 1 ^ γ) = nxt (VG γ) (Pv S η1)

/-- The statement of Theorem SEG at level `γ`. -/
def SEGst (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ η0 c0, Bt.Good S η0 → Om (1 : Ordinal.{0}) ^ γ ∣ η0 → γ < Pv S η0 → Pv S η0 = VG γ c0 →
    ∀ β ≤ Zu S η0 (Om 1 ^ γ), Pv S (η0 + Om 1 ^ γ * β) = VG γ (c0 + β)

theorem seg_of_start {γ : Ordinal.{0}} (hst : STARTst S γ) : SEGst S γ := by
  intro η0 c0 hg0 hdvd hγ h0
  refine aseg (VG_normal γ) (Om1_pow_pos γ) h0 fun β' hβ' ih => ?_
  set η1 := η0 + Om (1 : Ordinal.{0}) ^ γ * β' with hη1
  have hβP : β' < Pv S η1 := lt_Pv_of_lt_Zu hβ'
  have hγ1 : γ < Pv S η1 := hγ.trans_le (Pv_mono le_self_add)
  have hg1 : Bt.Good S η1 := good_add hg0 (mem_Om1_pow_mul hγ1 hβP)
  have hd1 : Om (1 : Ordinal.{0}) ^ γ ∣ η1 := dvd_add hdvd (dvd_mul_right _ _)
  have hC : ∀ δ < γ, δ < nxt (VG δ) (Pv S η1) := fun δ hδ =>
    (hδ.trans hγ1).trans (lt_nxt (VG_normal δ) (VG_at_zero δ) _)
  have := hst η1 hg1 hd1 hC
  rw [ih, nxt_apply (VG_normal γ) (VG_at_zero γ)] at this
  rw [mul_add_one, ← add_assoc]
  exact this

theorem start_zero (S : InaccSeq.{0}) : STARTst S 0 := by
  intro η1 hg _ _
  rw [opow_zero, VG_zero]
  have h1 := ups_iota S η1
  have h2 := ups_iota S (η1 + 1)
  rw [iota_good hg] at h2
  show S.psi (ConjT.Aη S (η1 + 1)) (Om 1) = nxt upsilon (S.psi (ConjT.Aη S η1) (Om 1))
  rw [← h1, ← h2, nxt_apply upsilon_normal upsilon_zero]

/-- The core of Theorem START at a successor level `γ+1`: the fixed point `Z'` of the segment of
`η₁ + Ω₁^γ` is the least value of `V_{γ+1}` above `P(η₁)`, and the values in that segment. -/
theorem succ_core {γ : Ordinal.{0}} (hst : STARTst S γ) {η1 : Ordinal.{0}} (hg : Bt.Good S η1)
    (hdvd : Om (1 : Ordinal.{0}) ^ γ ∣ η1) (hC : ∀ δ < γ + 1, δ < nxt (VG δ) (Pv S η1)) :
    ∃ c', Pv S (η1 + Om 1 ^ γ) = VG γ c' ∧
      (∀ β ≤ Zu S (η1 + Om 1 ^ γ) (Om 1 ^ γ),
        Pv S (η1 + Om 1 ^ γ + Om 1 ^ γ * β) = VG γ (c' + β)) ∧
      c' < Zu S (η1 + Om 1 ^ γ) (Om 1 ^ γ) ∧
      Zu S (η1 + Om 1 ^ γ) (Om 1 ^ γ) = nxt (VG (γ + 1)) (Pv S η1) := by
  set x1 := Pv S η1 with hx1
  have h1 := hst η1 hg hdvd fun δ hδ => hC δ (hδ.trans (lt_add_one γ))
  obtain ⟨c', hc'⟩ := nxt_mem (VG γ) x1
  set η1' := η1 + Om (1 : Ordinal.{0}) ^ γ with hη1'
  set Z' := Zu S η1' (Om 1 ^ γ) with hZ'
  have hy1 : Pv S η1' = VG γ c' := h1.trans hc'.symm
  have hγy : γ < Pv S η1' := by rw [h1]; exact hC γ (lt_add_one γ)
  have hg' : Bt.Good S η1' := good_add hg (mem_Om1_pow hγy)
  have hseg := seg_of_start hst η1' c' hg' (dvd_add hdvd dvd_rfl) hγy hy1
  have hZSC : SC Z' := Zu_SC S η1' _
  have hfix : Pv S (η1' + Om 1 ^ γ * Z') = Z' := Zu_fix S η1' _
  -- `P(η₁') < Z'`
  have hyZ : Pv S η1' < Z' := by
    by_contra hle
    rw [not_lt] at hle
    have hle2 : Pv S (η1' + 1) ≤ Pv S (η1' + Om 1 ^ γ * Z') := by
      refine Pv_mono ((add_le_add_iff_left _).2 ?_)
      exact Order.one_le_iff_pos.2 (mul_pos (Om1_pow_pos γ) hZSC.1)
    have := (Pv_lt_succ hg').trans_le hle2
    rw [hfix] at this
    exact absurd (this.trans_le hle) (lt_irrefl _)
  have hcZ : c' < Z' := ((VG_id_le γ c').trans hy1.symm.le).trans_lt hyZ
  have hVZ : VG γ Z' = Z' := by
    have := hseg Z' le_rfl
    rw [hfix, hZSC.isPrincipal.add_eq_right hcZ] at this
    exact this.symm
  have hx1y : x1 < Pv S η1' := by rw [h1]; exact lt_nxt (VG_normal γ) (VG_at_zero γ) x1
  refine ⟨c', hy1, hseg, hcZ, le_antisymm ?_ ?_⟩
  · -- `nxt V_{γ+1} x₁ ≥ Z'`
    by_contra hlt
    rw [not_le] at hlt
    set w := nxt (VG (γ + 1)) x1 with hw
    have hwfix : VG γ w = w := mem_range_VG_succ.1 (nxt_mem _ _)
    have hxw : x1 < w := lt_nxt (VG_normal _) (VG_at_zero _) x1
    have hyw : Pv S η1' ≤ w := by
      rw [h1]; exact nxt_le (VG_normal γ) (VG_at_zero γ) ⟨w, hwfix⟩ hxw
    have hyw' : Pv S η1' < w := by
      refine lt_of_le_of_ne hyw fun e => ?_
      rw [h1] at e
      exact nxt_not_fix γ x1 (by rw [e]; exact hwfix)
    have hcw : c' < w := by
      rw [hy1, ← hwfix] at hyw'; exact (VG_strictMono γ).lt_iff_lt.1 hyw'
    have h2 := lt_Pv_of_lt_Zu hlt
    have hwp : IsPrincipal (· + ·) w := by rw [← hwfix]; exact VG_principal γ w
    rw [hseg w hlt.le, hwp.add_eq_right hcw, hwfix] at h2
    exact lt_irrefl _ h2
  · exact nxt_le (VG_normal _) (VG_at_zero _) (mem_range_VG_succ.2 hVZ) (hx1y.trans hyZ)

theorem start_succ {γ : Ordinal.{0}} (hst : STARTst S γ) : STARTst S (γ + 1) := by
  intro η1 hg hdvd hC
  have hdvd' : Om (1 : Ordinal.{0}) ^ γ ∣ η1 :=
    dvd_trans ⟨Om 1, by rw [opow_add, opow_one]⟩ hdvd
  obtain ⟨c', hy1, hseg, hcZ, hZ⟩ := succ_core hst hg hdvd' hC
  rw [← hZ]
  set x1 := Pv S η1 with hx1
  set η1' := η1 + Om (1 : Ordinal.{0}) ^ γ with hη1'
  set Z' := Zu S η1' (Om 1 ^ γ) with hZ'
  have hZSC : SC Z' := Zu_SC S η1' _
  have hZ1 : Z' < Om 1 := Zu_lt_Om1 S η1' _
  have hfix : Pv S (η1' + Om 1 ^ γ * Z') = Z' := Zu_fix S η1' _
  have hVZ : VG γ Z' = Z' := by
    have := hseg Z' le_rfl
    rw [hfix, hZSC.isPrincipal.add_eq_right hcZ] at this
    exact this.symm
  have hxZ : x1 < Z' := by
    have := lt_nxt (VG_normal (γ + 1)) (VG_at_zero _) x1; rwa [← hZ] at this
  have hγΩ : γ ≤ Om 1 := by
    have := hC γ (lt_add_one γ)
    refine (this.trans ?_).le
    have h1 := hst η1 hg hdvd' fun δ hδ => hC δ (hδ.trans (lt_add_one γ))
    rw [← h1]; exact Pv_lt_Om1 S _
  apply le_antisymm
  · -- the jump
    refine psi_le_of_key hZSC fun e he hea => ?_
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with he1 | he1
    · calc S.psi e (Om 1) ≤ Pv S 0 := by rw [Pv, A_zero]; exact (psi_mono Low.InR_Om_one he1.le).1
        _ ≤ x1 := Pv_mono zero_le
        _ < Z' := hxZ
    obtain ⟨η, hη, k1, k2⟩ := quotA hZ1 he he1
    have hψ : S.psi e (Om 1) ≤ Pv S (η + 1) := by
      rw [Pv, ← ConjT.A_succ]; exact (psi_mono Low.InR_Om_one k2.le).1
    have hηlt : η < η1 + Om 1 ^ (γ + 1) := A_lt_A_iff.1 (k1.trans_lt hea)
    rcases lt_or_ge η η1 with hlt | hge
    · exact hψ.trans_lt ((Pv_mono (Order.add_one_le_of_lt hlt)).trans_lt hxZ)
    obtain ⟨q, z, r, hz, hr, hq⟩ := linvG_HCl hZSC hZ1 hγΩ hη
    obtain ⟨q1, hq1⟩ := hdvd
    have hU0 : Om (1 : Ordinal.{0}) ^ (γ + 1) ≠ 0 := (Om1_pow_pos _).ne'
    have hlow : Om 1 ^ γ * z + r < Om (1 : Ordinal.{0}) ^ (γ + 1) := by
      calc Om 1 ^ γ * z + r < Om 1 ^ γ * z + Om 1 ^ γ := (add_lt_add_iff_left _).2 hr
        _ = Om 1 ^ γ * (z + 1) := (mul_add_one _ _).symm
        _ ≤ Om 1 ^ γ * Om 1 := by gcongr; exact Order.add_one_le_of_lt (hz.trans hZ1)
        _ = Om 1 ^ (γ + 1) := by rw [opow_add, opow_one]
    have hq' : q = q1 := quot_eq hU0 hlow (by rw [hq, add_assoc]) (hq1 ▸ hge)
      (by rw [← hq1]; exact hηlt)
    subst hq'
    have hηe : η = η1 + (Om 1 ^ γ * z + r) := by rw [hq, hq1, add_assoc]
    have hle : η + 1 ≤ η1' + Om 1 ^ γ * (z + 1) := by
      rw [hηe, hη1', add_assoc, add_assoc, add_assoc]
      refine (add_le_add_iff_left η1).2 ?_
      calc Om 1 ^ γ * z + (r + 1) ≤ Om 1 ^ γ * z + Om 1 ^ γ :=
            (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hr)
        _ = Om 1 ^ γ * (z + 1) := (mul_add_one _ _).symm
        _ ≤ Om 1 ^ γ + Om 1 ^ γ * (z + 1) := le_add_self
    have hz1 : z + 1 ≤ Z' := Order.add_one_le_of_lt hz
    calc S.psi e (Om 1) ≤ Pv S (η + 1) := hψ
      _ ≤ Pv S (η1' + Om 1 ^ γ * (z + 1)) := Pv_mono hle
      _ = VG γ (c' + (z + 1)) := hseg (z + 1) hz1
      _ < VG γ Z' := (VG_strictMono γ) (hZSC.isPrincipal hcZ (hZSC.add_one_lt hz))
      _ = Z' := hVZ
  · -- the lower bound
    have hZ1' : Z' ≤ Om 1 := hZ1.le
    calc Z' = Pv S (η1' + Om 1 ^ γ * Z') := hfix.symm
      _ ≤ Pv S (η1 + Om 1 ^ (γ + 1)) := by
        refine Pv_mono ?_
        rw [hη1', add_assoc, ← mul_one_add, (hZSC.isPrincipal.add_eq_right (one_lt_SC hZSC)),
          opow_add, opow_one]
        gcongr

theorem start_limit {γ : Ordinal.{0}} (hl : IsSuccLimit γ) (IH : ∀ δ < γ, STARTst S δ) :
    STARTst S γ := by
  intro η1 hg hdvd hC
  set x1 := Pv S η1 with hx1
  have hγ0 : γ ≠ 0 := hl.ne_bot
  have hdvdδ : ∀ δ ≤ γ, Om (1 : Ordinal.{0}) ^ δ ∣ η1 := fun δ hδ =>
    dvd_trans ⟨Om 1 ^ (γ - δ), by rw [← opow_add, Ordinal.add_sub_cancel_of_le hδ]⟩ hdvd
  have hval : ∀ δ < γ, Pv S (η1 + Om 1 ^ δ) = nxt (VG δ) x1 := fun δ hδ =>
    IH δ hδ η1 hg (hdvdδ δ hδ.le) fun δ' hδ' => hC δ' (hδ'.trans hδ)
  have hXl : IsSuccLimit (Om (1 : Ordinal.{0}) ^ γ) := isSuccLimit_opow one_lt_Om1 hl
  -- every value below `P(η₁ + Ω₁^γ)` is below some `P(η₁ + Ω₁^δ)`
  have hcof : ∀ v < Pv S (η1 + Om 1 ^ γ), ∃ δ < γ, v < Pv S (η1 + Om 1 ^ δ) := by
    intro v hv
    by_contra hno
    simp only [not_exists, not_and, not_lt] at hno
    refine absurd (cont_le hXl fun c hc => ?_) (not_le.2 hv)
    obtain ⟨δ, hδ, hcδ⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans one_lt_Om1).ne' hl).1 hc
    exact (Pv_mono ((add_le_add_iff_left _).2 hcδ.le)).trans (hno δ hδ)
  apply le_antisymm
  · refine cont_le hXl fun c hc => ?_
    obtain ⟨δ, hδ, hcδ⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans one_lt_Om1).ne' hl).1 hc
    refine (Pv_mono ((add_le_add_iff_left _).2 hcδ.le)).trans ?_
    rw [hval δ hδ]
    exact nxt_le (VG_normal δ) (VG_at_zero δ) (range_VG_anti hδ.le (nxt_mem _ _))
      (lt_nxt (VG_normal γ) (VG_at_zero γ) x1)
  · set v := Pv S (η1 + Om 1 ^ γ) with hv
    have hxv : x1 < v := (Pv_lt_succ hg).trans_le
      (Pv_mono ((add_le_add_iff_left _).2 (Order.one_le_iff_pos.2 (Om1_pow_pos γ))))
    refine nxt_le (VG_normal γ) (VG_at_zero γ) ((mem_range_VG hγ0).2 fun b hb => ?_) hxv
    refine le_antisymm ?_ (VG_id_le b v)
    refine ((VG_normal b).le_iff_forall_le (Pv_SC S _).isSuccLimit).2 fun v' hv' => ?_
    obtain ⟨δ, hδ, hvδ⟩ := hcof v' hv'
    set δ' := max δ (b + 1) with hδ'
    have hδ'γ : δ' < γ := max_lt hδ (hl.add_one_lt hb)
    have hvδ' : v' < Pv S (η1 + Om 1 ^ δ') :=
      hvδ.trans_le (Pv_mono ((add_le_add_iff_left _).2 (Om1_pow_le_iff.2 (le_max_left _ _))))
    have hfixb : VG b (Pv S (η1 + Om 1 ^ δ')) = Pv S (η1 + Om 1 ^ δ') := by
      rw [hval δ' hδ'γ]
      obtain ⟨c, hc⟩ := nxt_mem (VG δ') x1
      rw [← hc]
      exact VG_VG ((lt_add_one b).trans_le (le_max_right _ _)) c
    calc VG b v' ≤ VG b (Pv S (η1 + Om 1 ^ δ')) := (VG_strictMono b).monotone hvδ'.le
      _ = Pv S (η1 + Om 1 ^ δ') := hfixb
      _ ≤ v := Pv_mono ((add_le_add_iff_left _).2 (Om1_pow_le_iff.2 hδ'γ.le))

/-- **Theorem START** at every level. -/
theorem start_all (S : InaccSeq.{0}) : ∀ γ, STARTst S γ := by
  intro γ
  induction γ using Ordinal.limitRecOn with
  | zero => exact start_zero S
  | add_one γ ih => exact start_succ ih
  | limit γ hl ih => exact start_limit hl ih

/-- **Theorem SEG** at every level. -/
theorem seg_all (S : InaccSeq.{0}) (γ : Ordinal.{0}) : SEGst S γ := seg_of_start (start_all S γ)

/-- The fixed point of the segment of `η₁ + Ω₁^γ`: `Zu (η₁ + Ω₁^γ) Ω₁^γ = nxt V_{γ+1} (P(η₁))`. -/
theorem zu_eq_nxt {γ η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hdvd : Om (1 : Ordinal.{0}) ^ γ ∣ η1)
    (hC : ∀ δ < γ + 1, δ < nxt (VG δ) (Pv S η1)) :
    Zu S (η1 + Om 1 ^ γ) (Om 1 ^ γ) = nxt (VG (γ + 1)) (Pv S η1) :=
  (succ_core (start_all S γ) hg hdvd hC).choose_spec.2.2.2

end Googology.Trans.PoR.InaccPsi.R2.Nm
