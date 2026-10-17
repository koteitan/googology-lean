import Googology.Trans.PoR.InaccPsi.R2.BrB

/-!
# Lemmas N, N2, Q and M for the map `B`

Paper proof of Theorem STEP (InaccPsi README): Lemma N (normality of the image arguments), Lemma N2,
Claim Q, Lemma M (`B` is strictly increasing on normal terms).  Induction: outer on the larger size,
inner on the sum of the sizes; Lemma N for `ϑ̄ᵢ(α)` uses Lemma M only for pairs of proper subterms.
Cited facts used: [W25] Lemma 2.12 (`W25_lem212`), Lemma 2.13 (`W25_lem213`), Proposition 2.15
(`W25_prop215`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

/-- The summands of a sum term. -/
def summands : Tm → List Tm
  | .par c => [par c]
  | .th j t => [th j t]
  | .add s r => summands s ++ summands r

theorem summ_size {r u : Tm} (h : u ∈ summands r) : size u ≤ size r := by
  induction r with
  | par c => simp [summands] at h; subst h; exact le_rfl
  | th j t _ => simp [summands] at h; subst h; exact le_rfl
  | add s r ihs ihr =>
    simp only [summands, List.mem_append] at h
    rcases h with h | h
    · have := ihs h; simp [size]; omega
    · have := ihr h; simp [size]; omega

namespace BP

variable {P : BP}

theorem summ_NF {r u : Tm} (hr : NF P.τ r) (h : u ∈ summands r) : NF P.τ u := by
  induction hr with
  | cpar hc => simp [summands] at h; subst h; exact NF.cpar hc
  | cth hu hd _ => simp [summands] at h; subst h; exact NF.cth hu hd
  | cadd h1 _ _ _ ih1 ih2 =>
    simp only [summands, List.mem_append] at h
    rcases h with h | h
    · exact ih1 h
    · exact ih2 h

theorem summ_le {r u : Tm} (hr : NF P.τ r) (h : u ∈ summands r) : ev P.τ u ≤ hd P.τ r := by
  induction hr with
  | cpar _ => simp [summands] at h; subst h; exact le_rfl
  | cth _ _ _ => simp [summands] at h; subst h; exact le_rfl
  | cadd h1 _ _ hle ih1 ih2 =>
    simp only [summands, List.mem_append] at h
    rcases h with h | h
    · exact ih1 h
    · exact (ih2 h).trans hle

theorem summ_shape {r u : Tm} (h : u ∈ summands r) : (∃ c, u = par c) ∨ ∃ j t, u = th j t := by
  induction r with
  | par c => simp [summands] at h; left; exact ⟨c, h⟩
  | th j t _ => simp [summands] at h; right; exact ⟨j, t, h⟩
  | add s r ihs ihr =>
    simp only [summands, List.mem_append] at h
    rcases h with h | h
    · exact ihs h
    · exact ihr h

theorem B_lt_of_summ {r : Tm} (hr : NF P.τ r) {Q : Ordinal.{0}} (hQ : IsPrincipal (· + ·) Q)
    (h : ∀ u ∈ summands r, P.B u < Q) : P.B r < Q := by
  induction hr with
  | cpar _ => exact h _ (by simp [summands])
  | cth _ _ _ => exact h _ (by simp [summands])
  | cadd _ _ _ _ ih1 ih2 =>
    rw [B_add]
    simp only [summands, List.mem_append] at h
    exact hQ (ih1 fun u hu => h u (Or.inl hu)) (ih2 fun u hu => h u (Or.inr hu))

/-! ## Lemma M as a predicate -/

/-- Lemma M for terms of size at most `n`. -/
def MR (P : BP) (n : ℕ) : Prop :=
  ∀ x y : Tm, size x ≤ n → size y ≤ n → NF P.τ x → NF P.τ y → ev P.τ x < ev P.τ y → P.B x < P.B y

theorem MR.mono {m n : ℕ} (h : P.MR n) (hmn : m ≤ n) : P.MR m :=
  fun x y hx hy => h x y (hx.trans hmn) (hy.trans hmn)

/-! ## The Remark: level-`i` parts reached through levels `≥ i` are at most `α^{*i}` -/

theorem rem (H : P.Hyp) (i : ℕ) : ∀ (n : ℕ) (α : Tm), size α ≤ n → NF P.τ α →
    ∀ η, (i, η) ∈ Kst i α → ev P.τ (th i η) ≤ Tm.star P.τ i α := by
  intro n
  induction n with
  | zero => intro α h; exact absurd (size_pos α) (by omega)
  | succ n ih =>
    intro α hs hα η hη
    rcases Kst_same hη with h | ⟨ηs, h1, h2⟩
    · exact le_star h
    · have hn := NF.Ki hα h1
      obtain ⟨_, -, hsz⟩ := Ki_shape h1
      have hle := ih ηs (by simp [size] at hsz; omega) (NF.th_arg hn) η h2
      have hlt := W25_lem212 H.base (NF.th_arg hn) i (NF.th_dom hn)
      exact (hle.trans hlt.le).trans (le_star h1)

/-- The level-`i` case of the bound in Lemma N. -/
theorem a_lt_same (H : P.Hyp) {i : ℕ} {α : Tm} (hM : P.MR (size α)) (hα : NF P.τ α) {η : Tm}
    (hη : (i, η) ∈ Kst i α) : P.a i η < P.a i α := by
  have hr := rem H i (size α) α le_rfl hα η hη
  have hnη : NF P.τ (th i η) := NF.Kst hα hη
  rcases P.top_spec i α with ⟨_, h2⟩ | ⟨δ, h1, h2, h3⟩
  · rw [h2] at hr
    exact absurd hr (not_le.2 (thb_pos H.base (NF.th_dom hnη)))
  · have hnδ : NF P.τ (th i δ) := NF.Ki hα h2
    have hlt : P.a i δ < P.a i α := by
      unfold a; rw [h1]
      exact lt_of_lt_of_le (lt_add_one _) le_self_add
    rw [h3] at hr
    rcases eq_or_lt_of_le hr with he | he
    · have := NF.unique H.base hnη hnδ he
      cases this
      exact hlt
    · have hsη := Kst_size hη
      obtain ⟨_, -, hsδ⟩ := Ki_shape h2
      exact (a_lt_of_B_lt (hM _ _ hsη hsδ hnη hnδ he)).trans hlt

/-! ## Claim Q -/

/-- **Claim Q.**  For `x ∈ dom(ϑ̄ᵢ)` and `(k, η) ∈ K*_{i+1}(x)`: `aₖ(η) < ω^{B(x)}`. -/
theorem QLem (H : P.Hyp) {i : ℕ} {x : Tm} (hM : P.MR (size x)) (hx : NF P.τ x)
    (hd : Dom P.τ i (ev P.τ x)) : ∀ (m : ℕ) (k : ℕ) (η : Tm), size η ≤ m →
      (k, η) ∈ Kst (i + 1) x → P.a k η < ω ^ P.B x := by
  intro m
  induction m with
  | zero => intro k η h; exact absurd (size_pos η) (by omega)
  | succ m ih =>
    intro k η hs hmem
    have hk : i + 1 ≤ k := Kst_level hmem
    have hcode : P.code k (ω ^ P.B η) = ω ^ P.B η := code_ne _ _ _ (fun h => by omega)
    have hev : ev P.τ η < ev P.τ x := (W25_lem213 H.base hx i).1 hd (k, η) hmem
    have hnη : NF P.τ η := NF.th_arg (NF.Kst hx hmem)
    have hsz := Kst_size hmem
    have hB : P.B η < P.B x := hM η x (by simp [size] at hsz; omega) le_rfl hnη hx hev
    have hw : ω ^ P.B η < ω ^ P.B x := (opow_lt_opow_iff_right one_lt_omega0).2 hB
    have hP : IsPrincipal (· + ·) (ω ^ P.B x) := isPrincipal_add_omega0_opow _
    have h1 : 1 < ω ^ P.B x := lt_of_le_of_lt (Order.one_le_iff_ne_zero.2 (opow_ne_zero _
      omega0_ne_zero)) hw
    unfold a; rw [hcode]
    rcases P.top_spec k η with ⟨h1', _⟩ | ⟨δ, e1, e2, _⟩
    · rw [h1']; simpa [cof] using hw
    · rw [e1]
      have hδ : (k, δ) ∈ Kst (i + 1) x := Kst_trans hmem (Ki_sub_Kst hk e2)
      obtain ⟨_, -, hsδ⟩ := Ki_shape e2
      have := ih k δ (by simp [size] at hsδ; omega) hδ
      exact hP (hP this h1) hw

/-! ## Lemma N and Lemma N2 -/

/-- **Lemma N.**  For a normal `ϑ̄ᵢ(α)`: `b := Xᵢ + aᵢ(α)` satisfies `b ∈ Cl(b, ψ_{Ω_{i+1}}(b))`, given
Lemma M for the proper subterms. -/
theorem NLem (H : P.Hyp) {i : ℕ} {α : Tm} (hM : P.MR (size α)) (hv : NF P.τ (th i α)) :
    P.X i + P.a i α ∈ P.S.CSet (P.X i + P.a i α) (P.S.psi (P.X i + P.a i α) (kap i)) := by
  set b := P.X i + P.a i α with hbdef
  set μ := P.S.psi b (kap i) with hμdef
  have hα : NF P.τ α := NF.th_arg hv
  have hdom : Dom P.τ i (ev P.τ α) := NF.th_dom hv
  -- `Ω_ω ≤ X₀ ≤ b` in mode `true`
  have hXb : P.X i ≤ b := le_self_add
  have hτμ : P.τ ≤ μ := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact H.tau_le.trans (psi_mono (kap_InR P.S 0) (by rw [X_zero] at hXb; exact hXb)).1
    · exact (tau_lt_Om_nat H hi.ne').le.trans (psiS_bounds b (i : Ordinal.{0})).1.le
  have hlow : ∀ k < i, kap k ≤ μ := fun k hk => (kap_le_Om hk).trans (psiS_bounds b _).1.le
  have hmdt : P.md = true → i = 0 → Om (ω : Ordinal.{0}) ≤ b := by
    intro hm hi; subst hi; rw [X_zero] at hXb; exact (H.md_true hm).1.trans hXb
  have hX : ∀ k, i ≤ k → P.X k ∈ P.S.CSet b μ := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have hi : i = 0 := by omega
      subst hi
      rw [X_zero]
      cases hm : P.md
      · rw [H.md_false hm]; exact CSet.zero_mem _ _
      · obtain ⟨-, hA⟩ := H.md_true hm
        refine CSet_mono ?_ (psi_mono (kap_InR P.S 0) ?_).1 hA
        · rw [hbdef, X_zero]
          refine add_le_add le_rfl (Order.one_le_iff_pos.2 ?_)
          refine lt_of_lt_of_le ?_ (code_le_a 0 α)
          rw [code_eq _ _ hm]; exact (SC_psi (kap_InR P.S 1) _).1
        · rw [hbdef, X_zero]; exact le_self_add
    · rw [X_ne _ hk0]; exact CSet.zero_mem _ _
  -- `ω^{B(x)} ≤ b` for the anchors
  have hW : ∀ x, NF P.τ x → (x = α ∨ (i, x) ∈ Kst i α) → ω ^ P.B x ≤ b := by
    intro x hx hxα
    by_cases hm : i = 0 ∧ P.md = true
    · have h1 : ω ^ P.B x < Om (ω : Ordinal.{0}) := by
        have := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero) _
          (B_lt_Om_omega H hx)
        rwa [veblen_zero_apply] at this
      exact (h1.trans_le (hmdt hm.2 hm.1)).le
    · have hc : ω ^ P.B x ≤ P.a i x := by
        have := code_le_a (P := P) i x; rwa [code_ne _ _ _ hm] at this
      rcases hxα with rfl | hxα
      · exact hc.trans le_add_self
      · exact hc.trans ((a_lt_same H hM hα hxα).le.trans le_add_self)
  have hb : ∀ p ∈ Kst i α, P.X p.1 + P.a p.1 p.2 < b := by
    rintro ⟨k, η⟩ hp
    have hik : i ≤ k := Kst_level hp
    rcases eq_or_lt_of_le hik with rfl | hlt
    · exact add_lt_add_right (a_lt_same H hM hα hp) _
    · rw [X_ne _ (by omega), zero_add]
      rcases Kst_anchor hp hlt with h | ⟨ηs, h1, h2⟩
      · exact lt_of_lt_of_le (QLem H hM hα hdom _ k η le_rfl h) (hW α hα (Or.inl rfl))
      · have hns : NF P.τ (th i ηs) := NF.Kst hα h1
        have hsz := Kst_size h1
        have hMs : P.MR (size ηs) := hM.mono (by simp [size] at hsz; omega)
        exact lt_of_lt_of_le (QLem H hMs (NF.th_arg hns) (NF.th_dom hns) _ k η le_rfl h2)
          (hW ηs (NF.th_arg hns) (Or.inr h1))
  have hcode : ∀ p ∈ Kst i α, p.1 = 0 → P.md = true → ω ^ P.B p.2 < b := by
    intro p hp h0 hm
    have hi : i = 0 := by have := Kst_level hp; omega
    have h1 : ω ^ P.B p.2 < Om (ω : Ordinal.{0}) := by
      have := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero) _
        (B_lt_Om_omega H (NF.th_arg (NF.Kst hα hp)))
      rwa [veblen_zero_apply] at this
    exact h1.trans_le (hmdt hm hi)
  obtain ⟨gB, ga⟩ := gen H i b μ hτμ hlow hX hα hb hcode
  refine CSet.add_mem (hX i le_rfl) ?_
  unfold a
  refine CSet.add_mem ?_ ?_
  · rcases P.top_spec i α with ⟨h1, _⟩ | ⟨δ, h1, h2, _⟩
    · rw [h1]; exact CSet.zero_mem _ _
    · rw [h1]; exact CSet.succ_mem (ga (i, δ) (Ki_sub_Kst le_rfl h2))
  · have hw : ω ^ P.B α ∈ P.S.CSet b μ := by
      have := CSet.phi_mem (CSet.zero_mem (S := P.S) b μ) gB
      rwa [veblen_zero_apply] at this
    by_cases hm : i = 0 ∧ P.md = true
    · unfold code; rw [if_pos hm]
      have h1 : ω ^ P.B α < Om (ω : Ordinal.{0}) := by
        have := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero) _
          (B_lt_Om_omega H hα)
        rwa [veblen_zero_apply] at this
      have hlt : ω ^ P.B α < b := by
        refine lt_of_lt_of_le h1 ((hmdt hm.2 hm.1).trans ?_)
        exact le_rfl
      exact CSet.psi_mem hlt (kap_InR P.S 1) (kap_mem 1 _ _) hw
    · rw [code_ne _ _ _ hm]; exact hw

theorem kap_one : kap 1 = Om ((1 : Ordinal.{0}) + 1) := by unfold kap; simp

/-- **Lemma N2** (mode `true`): `e := ω^{B(α)}` satisfies `e ∈ Cl(e, ψ_{Ω₂}(e))` for `α ∈ dom(ϑ̄₀)`. -/
theorem N2Lem (H : P.Hyp) {α : Tm} (hM : P.MR (size α)) (hα : NF P.τ α)
    (hd : Dom P.τ 0 (ev P.τ α)) :
    ω ^ P.B α ∈ P.S.CSet (ω ^ P.B α) (P.S.psi (ω ^ P.B α) (kap 1)) := by
  set e := ω ^ P.B α with hedef
  set μ := P.S.psi e (kap 1) with hμdef
  have hOm1 : Om (1 : Ordinal.{0}) < μ := by
    have := (psiS_bounds (S := P.S) e ((1 : ℕ) : Ordinal.{0})).1
    rw [hμdef, kap_one]; simpa using this
  have hτμ : P.τ ≤ μ := (H.base.lt_Om1.trans hOm1).le
  have hlow : ∀ k < 1, kap k ≤ μ := by
    intro k hk
    have : k = 0 := by omega
    subst this; rw [kap_zero]; exact hOm1.le
  have hX : ∀ k, 1 ≤ k → P.X k ∈ P.S.CSet e μ := by
    intro k hk; rw [X_ne _ (by omega)]; exact CSet.zero_mem _ _
  have hb : ∀ p ∈ Kst 1 α, P.X p.1 + P.a p.1 p.2 < e := by
    rintro ⟨k, η⟩ hp
    have hk := Kst_level hp
    rw [X_ne _ (by simp at hk; omega), zero_add]
    exact QLem H hM hα hd _ k η le_rfl hp
  have hcode : ∀ p ∈ Kst 1 α, p.1 = 0 → P.md = true → ω ^ P.B p.2 < e := by
    intro p hp h0; have := Kst_level hp; omega
  obtain ⟨gB, _⟩ := gen H 1 e μ hτμ hlow hX hα hb hcode
  have := CSet.phi_mem (CSet.zero_mem (S := P.S) e μ) gB
  rwa [veblen_zero_apply] at this

/-! ## Lemma M -/

/-- A sum whose leading part is below a `ϑ̄`-term `Y` is sent below `B(Y)`, given Lemma M for its summands. -/
theorem B_lt_th_of (H : P.Hyp) {r : Tm} {j : ℕ} {β : Tm} (hr : NF P.τ r) (hlt : hd P.τ r < ev P.τ (th j β))
    (orc : ∀ u ∈ summands r, NF P.τ u → ev P.τ u < ev P.τ (th j β) → P.B u < P.B (th j β)) :
    P.B r < P.B (th j β) := by
  refine B_lt_of_summ hr (P.B_th_principal j β) fun u hu => ?_
  have hnu := summ_NF hr hu
  rcases summ_shape hu with ⟨c, rfl⟩ | ⟨k, t, rfl⟩
  · rw [B_par]; exact lt_of_lt_of_le (NF.par_lt hnu) (tau_le_B_th H j β)
  · exact orc _ hu hnu (lt_of_le_of_lt (summ_le hr hu) hlt)

/-- The principal case of Lemma M: `ϑ̄ᵢ(α) < ϑ̄ⱼ(β)`. -/
theorem PM (H : P.Hyp) {n : ℕ} (IHo : P.MR n) {i j : ℕ} {α β : Tm} (hx : size (th i α) ≤ n + 1)
    (hy : size (th j β) ≤ n + 1)
    (IHi : ∀ x' y', size x' ≤ n + 1 → size y' ≤ n + 1 → size x' + size y' < size (th i α) + size (th j β) →
      NF P.τ x' → NF P.τ y' → ev P.τ x' < ev P.τ y' → P.B x' < P.B y')
    (nx : NF P.τ (th i α)) (ny : NF P.τ (th j β)) (hlt : ev P.τ (th i α) < ev P.τ (th j β)) :
    P.B (th i α) < P.B (th j β) := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact (P.B_th_bounds i α).2.trans_le ((kap_le_Om hij).trans (P.B_th_bounds j β).1.le)
  swap
  · have h1 := (NF.th_bounds H.base ny).2
    have h2 := OmT_mono H.base (Nat.succ_le_of_lt hij)
    have h3 := (NF.th_bounds H.base nx).1
    exact absurd hlt (not_lt.2 (h1.trans_le (h2.trans h3)).le)
  have hα := NF.th_arg nx
  have hβ := NF.th_arg ny
  have hdα := NF.th_dom nx
  have hdβ := NF.th_dom ny
  have hsα : size α ≤ n := by simp only [size] at hx; omega
  have hsβ : size β ≤ n := by simp only [size] at hy; omega
  have hMα : P.MR (size α) := IHo.mono hsα
  have hN := NLem H hMα nx
  suffices ha : P.a i α < P.a i β by
    rw [B_th, B_th]
    exact psi_lt_psi (kap_InR P.S i) (add_lt_add_right ha _) hN
  -- Case III, given `β^{*i} < ϑ̄ᵢ(α)`
  have case3 : Tm.star P.τ i β < ev P.τ (th i α) → P.a i α < P.a i β := by
    intro hq
    rcases (W25_prop215 H.base hα hβ i hdα hdβ).1 hlt with ⟨hαβ, hp⟩ | hle
    swap
    · exact absurd (lt_of_le_of_lt hle hq) (lt_irrefl _)
    have hBαβ : P.B α < P.B β := IHo α β hsα hsβ hα hβ hαβ
    have hw : ω ^ P.B α < ω ^ P.B β := (opow_lt_opow_iff_right one_lt_omega0).2 hBαβ
    have hcode : P.code i (ω ^ P.B α) < P.code i (ω ^ P.B β) ∧
        IsPrincipal (· + ·) (P.code i (ω ^ P.B β)) ∧ 1 < P.code i (ω ^ P.B β) := by
      by_cases hm : i = 0 ∧ P.md = true
      · obtain ⟨rfl, hm2⟩ := hm
        rw [code_eq _ _ hm2, code_eq _ _ hm2]
        refine ⟨psi_lt_psi (kap_InR P.S 1) hw (N2Lem H hMα hα hdα),
          (SC_psi (kap_InR P.S 1) _).isPrincipal, ?_⟩
        have := (psiS_bounds (S := P.S) (ω ^ P.B β) ((1 : ℕ) : Ordinal.{0})).1
        rw [kap_one]
        simp only [Nat.cast_one] at this
        exact lt_trans (one_lt_omega0.trans (omega0_lt_Om one_ne_zero)) this
      · rw [code_ne _ _ _ hm, code_ne _ _ _ hm]
        exact ⟨hw, isPrincipal_add_omega0_opow _, lt_of_le_of_lt
          (Order.one_le_iff_ne_zero.2 (opow_ne_zero _ omega0_ne_zero)) hw⟩
    obtain ⟨hc1, hP, h1P⟩ := hcode
    rcases P.top_spec i α with ⟨hp1, _⟩ | ⟨δp, hp1, hp2, hp3⟩
    · unfold a; rw [hp1]
      simp only [cof, zero_add]
      exact lt_of_lt_of_le hc1 le_add_self
    · have hnδp : NF P.τ (th i δp) := NF.Ki hα hp2
      obtain ⟨_, -, hsz⟩ := Ki_shape hp2
      have hδlt : ev P.τ (th i δp) < ev P.τ (th i β) := hp3 ▸ hp
      have hBδ := IHi _ _ (le_trans hsz (by omega)) hy
        (by have : size (th i α) = size α + 1 := rfl; omega) hnδp ny hδlt
      have haδ : P.a i δp < cof (P.top i β) + P.code i (ω ^ P.B β) := a_lt_of_B_lt hBδ
      have := ConjT.arith_absorb hP h1P haδ hc1
      unfold a; rw [hp1]
      simpa [cof] using this
  rcases P.top_spec i β with ⟨_, hq2⟩ | ⟨δ, hq1, hq2, hq3⟩
  · exact case3 (by rw [hq2]; exact thb_pos H.base hdα)
  · by_cases hcase : ev P.τ (th i α) ≤ ev P.τ (th i δ)
    · have hnδ : NF P.τ (th i δ) := NF.Ki hβ hq2
      have hcβ : P.a i δ < P.a i β := by
        unfold a; rw [hq1]; exact lt_of_lt_of_le (lt_add_one _) le_self_add
      rcases eq_or_lt_of_le hcase with he | he
      · have := NF.unique H.base nx hnδ he
        cases this
        exact hcβ
      · obtain ⟨_, -, hsz⟩ := Ki_shape hq2
        have hB := IHi _ _ hx (by simp only [size] at hy hsz ⊢; omega) (by simp only [size] at hsz ⊢; omega)
          nx hnδ he
        exact (a_lt_of_B_lt hB).trans hcβ
    · exact case3 (hq3 ▸ not_le.1 hcase)

/-- The inner step of Lemma M. -/
theorem M_step (H : P.Hyp) {n : ℕ} (IHo : P.MR n) {x y : Tm} (hx : size x ≤ n + 1)
    (hy : size y ≤ n + 1)
    (IHi : ∀ x' y', size x' ≤ n + 1 → size y' ≤ n + 1 → size x' + size y' < size x + size y →
      NF P.τ x' → NF P.τ y' → ev P.τ x' < ev P.τ y' → P.B x' < P.B y')
    (nx : NF P.τ x) (ny : NF P.τ y) (hlt : ev P.τ x < ev P.τ y) : P.B x < P.B y := by
  cases nx with
  | @cpar c hc =>
    rw [B_par]
    cases ny with
    | cpar _ => exact hlt
    | @cth j β _ _ => exact lt_of_lt_of_le hc (tau_le_B_th H j β)
    | @cadd j u r _ _ _ _ =>
      rw [B_add]; exact lt_of_lt_of_le hc ((tau_le_B_th H j u).trans le_self_add)
  | @cth i α hα hdα =>
    have nx' : NF P.τ (th i α) := NF.cth hα hdα
    cases ny with
    | @cpar d hd' => exact absurd (lt_trans hlt hd') (not_lt.2 (tau_le_th H.base nx'))
    | @cth j β hβ hdβ => exact PM H IHo hx hy IHi nx' (NF.cth hβ hdβ) hlt
    | @cadd j u r h1 h2 h3 h4 =>
      have ny' := NF.cadd h1 h2 h3 h4
      rcases lt_trichotomy (ev P.τ (th i α)) (ev P.τ (th j u)) with h | h | h
      · rw [B_add]
        exact lt_of_lt_of_le (IHi _ _ hx (by simp only [size] at hy ⊢; omega)
          (by simp only [size]; omega) nx' h1 h) le_self_add
      · have e := NF.unique H.base nx' h1 h
        rw [B_add, e]; exact lt_add_of_pos_right _ (B_pos H h2 h3)
      · exact absurd hlt (not_lt.2 (NF.ev_lt H.base ny' (NF.th_principal H.base nx') h).le)
  | @cadd i u r h1 h2 h3 h4 =>
    have nx' := NF.cadd h1 h2 h3 h4
    have hpos : ev P.τ (th i u) < ev P.τ (add (th i u) r) :=
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 (NF.ev_ne_zero H.base h2 h3))
    cases ny with
    | @cpar d hd' =>
      exact absurd (lt_trans hlt hd') (not_lt.2 ((tau_le_th H.base h1).trans le_self_add))
    | @cth j β hβ hdβ =>
      have ny' := NF.cth hβ hdβ
      have hh : ev P.τ (th i u) < ev P.τ (th j β) := lt_trans hpos hlt
      rw [B_add]
      refine P.B_th_principal j β (IHi _ _ (by simp only [size] at hx ⊢; omega) hy
        (by simp only [size]; omega) h1 ny' hh) ?_
      exact B_lt_th_of H h2 (lt_of_le_of_lt h4 hh) fun u' hu' hnu' hlt' =>
        IHi u' _ ((summ_size hu').trans (by simp only [size] at hx ⊢; omega)) hy
          (by have := summ_size hu'; simp only [size]; omega) hnu' ny' hlt'
    | @cadd j v r' g1 g2 g3 g4 =>
      have ny' := NF.cadd g1 g2 g3 g4
      rcases lt_trichotomy (ev P.τ (th i u)) (ev P.τ (th j v)) with h | h | h
      · rw [B_add, B_add]
        refine lt_of_lt_of_le ?_ le_self_add
        refine P.B_th_principal j v (IHi _ _ (by simp only [size] at hx ⊢; omega)
          (by simp only [size] at hy ⊢; omega) (by simp only [size]; omega) h1 g1 h) ?_
        exact B_lt_th_of H h2 (lt_of_le_of_lt h4 h) fun u' hu' hnu' hlt' =>
          IHi u' _ ((summ_size hu').trans (by simp only [size] at hx ⊢; omega))
            (by simp only [size] at hy ⊢; omega) (by have := summ_size hu'; simp only [size]; omega) hnu' g1 hlt'
      · have e := NF.unique H.base h1 g1 h
        cases e
        have hr : ev P.τ r < ev P.τ r' := by
          have hlt' : ev P.τ (th i u) + ev P.τ r < ev P.τ (th i u) + ev P.τ r' := hlt
          exact (add_lt_add_iff_left _).1 hlt'
        rw [B_add, B_add]
        exact add_lt_add_right (IHi _ _ (by simp only [size] at hx ⊢; omega) (by simp only [size] at hy ⊢; omega)
          (by simp only [size]; omega) h2 g2 hr) _
      · have hy' : ev P.τ (add (th j v) r') < ev P.τ (th i u) :=
          NF.ev_lt H.base ny' (NF.th_principal H.base h1) h
        exact absurd (lt_trans hlt hy') (not_lt.2 hpos.le)

/-- **Lemma M.**  `B` is strictly increasing on normal terms. -/
theorem B_strictMono (H : P.Hyp) : ∀ n, P.MR n := by
  intro n
  induction n with
  | zero => intro x y hx; exact absurd (size_pos x) (by omega)
  | succ n IHo =>
    have key : ∀ m, ∀ x y : Tm, size x + size y ≤ m → size x ≤ n + 1 → size y ≤ n + 1 →
        NF P.τ x → NF P.τ y → ev P.τ x < ev P.τ y → P.B x < P.B y := by
      intro m
      induction m with
      | zero => intro x y hs; have := size_pos x; omega
      | succ m ihm =>
        intro x y hs hx hy nx ny hlt
        exact M_step H IHo hx hy (fun x' y' hx' hy' hs' => ihm x' y' (by omega) hx' hy') nx ny hlt
    intro x y hx hy
    exact key _ x y le_rfl hx hy

/-- Lemma M for all normal terms. -/
theorem B_lt (H : P.Hyp) {x y : Tm} (nx : NF P.τ x) (ny : NF P.τ y) (h : ev P.τ x < ev P.τ y) :
    P.B x < P.B y :=
  B_strictMono H (max (size x) (size y)) x y (le_max_left _ _) (le_max_right _ _) nx ny h

end BP

end Googology.Trans.PoR.InaccPsi.R2.Br
