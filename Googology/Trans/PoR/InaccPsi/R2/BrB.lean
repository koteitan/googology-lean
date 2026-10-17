import Googology.Trans.PoR.InaccPsi.R2.CitedBr
import Googology.Trans.PoR.InaccPsi.ConjT

/-!
# The map `B` from `T̄^τ` into InaccPsi, and its order preservation

The map `B` of the paper proof of Theorem STEP (InaccPsi README, Theorem STEP; the proof uses [W25]
Lemma 2.12, Lemma 2.13, Proposition 2.15, cited in `R2.CitedBr`).  Fix an InaccPsi sequence `S`, a base
`τ` (`Base τ`), an ordinal `X₀` and a mode `md`:
* `B(c) = c` for parameters `c < τ`; `B` of a normal sum is the sum of the `B` of the summands;
* `B(ϑ̄ᵢ(α)) = ψ_{Ω_{i+1}}(Xᵢ + aᵢ(α))`, `aᵢ(α) = cᵢ(α) + codeᵢ(ω^{B(α)})`, with `X₀` given and
  `Xᵢ = 0` (`i ≥ 1`), `codeᵢ(e) = e` except `code₀(e) = ψ_{Ω₂}(e)` in the mode `md = true`;
* `cᵢ(α) = 0` if `α^{*i} = 0`, and `cᵢ(α) = aᵢ(δ) + 1` if `α^{*i} = ϑ̄ᵢ(δ)` (the parameter lift).
`BT` computes `B(t)` together with, for every level `i`, the pair `(α^{*i}, aᵢ(δ))` of the largest member
`ϑ̄ᵢ(δ)` of `Kᵢ(t)`, by structural recursion.

Mode `md = false`, `X₀ = 0`, `τ = 1`: Theorem STEP-0.  Mode `md = true`, `X₀ = A` with `Ω_ω ≤ A`,
`τ ≤ ψ_{Ω₁}(A)` and (HA) `A ∈ Cl(A + 1, ψ_{Ω₁}(A))`: Theorem STEP.

Main results: `NLem` (Lemma N: each image argument lies in its own hull, so `ψ` is strictly increasing
there, InaccPsi F12), `N2Lem`, `QLem` (Claim Q), and `B_strictMono` (Lemma M: `x < y ⇒ B(x) < B(y)` for
normal terms).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

/-- The data of the map `B`. -/
structure BP where
  S : InaccSeq.{0}
  τ : Ordinal.{0}
  X0 : Ordinal.{0}
  md : Bool

/-- `cof none = 0`, `cof (some (v, a)) = a + 1`. -/
def cof : Option (Ordinal.{0} × Ordinal.{0}) → Ordinal.{0}
  | none => 0
  | some p => p.2 + 1

/-- The larger of two candidates (by the first component). -/
noncomputable def omax : Option (Ordinal.{0} × Ordinal.{0}) → Option (Ordinal.{0} × Ordinal.{0}) →
    Option (Ordinal.{0} × Ordinal.{0})
  | none, y => y
  | some p, none => some p
  | some p, some q => if q.1 ≤ p.1 then some p else some q

/-- `Ω_{i+1}`, the subscript of the image of a level-`i` term. -/
noncomputable def kap (i : ℕ) : Ordinal.{0} := Om ((i : Ordinal.{0}) + 1)

theorem kap_InR (S : InaccSeq.{0}) (i : ℕ) : S.InR (kap i) := InR_Om_succ _

namespace BP

variable (P : BP)

/-- `Xᵢ`. -/
noncomputable def X (i : ℕ) : Ordinal.{0} := if i = 0 then P.X0 else 0

/-- `codeᵢ`. -/
noncomputable def code (i : ℕ) (e : Ordinal.{0}) : Ordinal.{0} :=
  if i = 0 ∧ P.md = true then P.S.psi e (kap 1) else e

/-- `B` with the table of the largest level-`i` parts. -/
noncomputable def BT : Tm → Ordinal.{0} × (ℕ → Option (Ordinal.{0} × Ordinal.{0}))
  | .par c => (c, fun _ => none)
  | .add s r => ((BT s).1 + (BT r).1, fun i => omax ((BT s).2 i) ((BT r).2 i))
  | .th j t => (P.S.psi (P.X j + (cof ((BT t).2 j) + P.code j (ω ^ (BT t).1))) (kap j),
      fun i => if j < i then none else if j = i then
        some (ev P.τ (th j t), cof ((BT t).2 i) + P.code i (ω ^ (BT t).1)) else (BT t).2 i)

/-- `B`. -/
noncomputable def B (t : Tm) : Ordinal.{0} := (P.BT t).1

/-- The largest level-`i` part of `t` and the `aᵢ` of its argument. -/
noncomputable def top (i : ℕ) (t : Tm) : Option (Ordinal.{0} × Ordinal.{0}) := (P.BT t).2 i

/-- `aᵢ(t) = cᵢ(t) + codeᵢ(ω^{B(t)})`. -/
noncomputable def a (i : ℕ) (t : Tm) : Ordinal.{0} := cof (P.top i t) + P.code i (ω ^ P.B t)

theorem B_par (c : Ordinal.{0}) : P.B (par c) = c := rfl

theorem B_add (s r : Tm) : P.B (add s r) = P.B s + P.B r := rfl

theorem B_th (j : ℕ) (t : Tm) : P.B (th j t) = P.S.psi (P.X j + P.a j t) (kap j) := rfl

theorem top_par (i : ℕ) (c : Ordinal.{0}) : P.top i (par c) = none := rfl

theorem top_add (i : ℕ) (s r : Tm) : P.top i (add s r) = omax (P.top i s) (P.top i r) := rfl

theorem top_th (i j : ℕ) (t : Tm) : P.top i (th j t) =
    if j < i then none else if j = i then some (ev P.τ (th j t), P.a i t) else P.top i t := rfl

theorem code_ne (i : ℕ) (e : Ordinal.{0}) (h : ¬ (i = 0 ∧ P.md = true)) : P.code i e = e := by
  unfold code; rw [if_neg h]

theorem code_eq (e : Ordinal.{0}) (h : P.md = true) : P.code 0 e = P.S.psi e (kap 1) := by
  unfold code; rw [if_pos ⟨rfl, h⟩]

theorem X_ne {i : ℕ} (h : i ≠ 0) : P.X i = 0 := by unfold X; rw [if_neg h]

theorem X_zero : P.X 0 = P.X0 := rfl

theorem kap_zero : kap 0 = Om (1 : Ordinal.{0}) := by unfold kap; simp

/-- `B` of a level-`j` term lies in `(Ω_j, Ω_{j+1})` (InaccPsi F9). -/
theorem B_th_bounds (j : ℕ) (t : Tm) :
    Om (j : Ordinal.{0}) < P.B (th j t) ∧ P.B (th j t) < kap j :=
  psiS_bounds _ _

theorem B_th_principal (j : ℕ) (t : Tm) : IsPrincipal (· + ·) (P.B (th j t)) :=
  (SC_psi (kap_InR P.S j) _).isPrincipal

end BP

/-! ## Hypotheses -/

/-- The hypotheses on the data. -/
structure BP.Hyp (P : BP) : Prop where
  base : Base P.τ
  tau_le : P.τ ≤ P.S.psi P.X0 (kap 0)
  md_false : P.md = false → P.X0 = 0
  md_true : P.md = true → Om (ω : Ordinal.{0}) ≤ P.X0 ∧
    P.X0 ∈ P.S.CSet (P.X0 + 1) (P.S.psi P.X0 (kap 0))

namespace BP

variable {P : BP}

theorem natCast_mem (n : ℕ) (a b : Ordinal.{0}) : ((n : Ordinal.{0})) ∈ P.S.CSet a b := by
  induction n with
  | zero => simpa using CSet.zero_mem (S := P.S) a b
  | succ n ih => rw [Nat.cast_succ]; exact CSet.succ_mem ih

theorem kap_mem (i : ℕ) (a b : Ordinal.{0}) : kap i ∈ P.S.CSet a b :=
  CSet.Om_mem (CSet.succ_mem (natCast_mem i a b))

theorem Om_nat_le_Om_nat {i j : ℕ} (h : i ≤ j) : Om (i : Ordinal.{0}) ≤ Om (j : Ordinal.{0}) :=
  Om_le_Om.2 (by exact_mod_cast h)

theorem kap_le_Om {i j : ℕ} (h : i < j) : kap i ≤ Om (j : Ordinal.{0}) := by
  unfold kap
  have : ((i : Ordinal.{0}) + 1) = ((i + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  rw [this]; exact Om_nat_le_Om_nat h

theorem kap_lt_Om_omega (i : ℕ) : kap i < Om (ω : Ordinal.{0}) := by
  unfold kap
  have : ((i : Ordinal.{0}) + 1) = ((i + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  rw [this]; exact Om_lt_Om_omega _

theorem Om_one_le_Om_nat {i : ℕ} (hi : i ≠ 0) : Om (1 : Ordinal.{0}) ≤ Om (i : Ordinal.{0}) := by
  have := Om_nat_le_Om_nat (i := 1) (j := i) (Nat.one_le_iff_ne_zero.2 hi)
  simpa using this

theorem tau_lt_Om_nat (H : P.Hyp) {i : ℕ} (hi : i ≠ 0) : P.τ < Om (i : Ordinal.{0}) :=
  lt_of_lt_of_le H.base.lt_Om1 (Om_one_le_Om_nat hi)

/-- `τ ≤ B(ϑ̄ⱼ(t))`. -/
theorem tau_le_B_th (H : P.Hyp) (j : ℕ) (t : Tm) : P.τ ≤ P.B (th j t) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [B_th, X_zero]
    exact H.tau_le.trans (psi_mono (kap_InR P.S 0) le_self_add).1
  · exact (tau_lt_Om_nat H hj.ne').le.trans (P.B_th_bounds j t).1.le

theorem B_lt_Om_omega (H : P.Hyp) {t : Tm} (ht : NF P.τ t) : P.B t < Om (ω : Ordinal.{0}) := by
  induction ht with
  | cpar hc => exact lt_of_lt_of_le hc (OmT_lt_Om_omega H.base 0 |>.le |> fun h =>
      (OmT_zero P.τ ▸ h))
  | @cth j u _ _ _ => exact (P.B_th_bounds j u).2.trans (kap_lt_Om_omega j)
  | cadd _ _ _ _ ih1 ih2 => exact Om_omega_principal ih1 ih2

theorem B_pos (_H : P.Hyp) {t : Tm} (ht : NF P.τ t) (h0 : t ≠ par 0) : 0 < P.B t := by
  cases ht with
  | @cpar c _ =>
    rw [B_par]; exact pos_iff_ne_zero.2 fun e => h0 (by rw [e])
  | @cth j u _ _ => exact lt_of_le_of_lt zero_le (P.B_th_bounds j u).1
  | @cadd j u r _ _ _ _ =>
    rw [B_add]; exact lt_of_lt_of_le (lt_of_le_of_lt zero_le (P.B_th_bounds j u).1) le_self_add

/-- Inverting `ψ`: `B(ϑ̄ᵢ(α)) < B(ϑ̄ᵢ(β))` gives `aᵢ(α) < aᵢ(β)` (InaccPsi F11). -/
theorem a_lt_of_B_lt {i : ℕ} {α β : Tm} (h : P.B (th i α) < P.B (th i β)) : P.a i α < P.a i β := by
  by_contra hle
  rw [not_lt] at hle
  rw [B_th, B_th] at h
  exact absurd h (not_lt.2 (psi_mono (kap_InR P.S i) (add_le_add le_rfl hle)).1)

/-! ## The table `top` -/

theorem foldr_max_append (l1 l2 : List Ordinal.{0}) :
    (l1 ++ l2).foldr max 0 = max (l1.foldr max 0) (l2.foldr max 0) := by
  induction l1 with
  | nil => simp
  | cons v l ih => simp only [List.cons_append, List.foldr_cons, ih, max_assoc]

theorem star_add (τ : Ordinal.{0}) (i : ℕ) (s r : Tm) :
    Tm.star τ i (add s r) = max (Tm.star τ i s) (Tm.star τ i r) := by
  unfold Tm.star; simp only [Ki, List.map_append, foldr_max_append]

/-- **The table**: `top i t` is `none` with `t^{*i} = 0`, or `(ϑ̄ᵢ(δ), aᵢ(δ))` for a member `ϑ̄ᵢ(δ)` of
`Kᵢ(t)` with `t^{*i} = ϑ̄ᵢ(δ)`. -/
theorem top_spec (i : ℕ) (t : Tm) :
    (P.top i t = none ∧ Tm.star P.τ i t = 0) ∨
      ∃ δ, P.top i t = some (ev P.τ (th i δ), P.a i δ) ∧ th i δ ∈ Ki i t ∧
        Tm.star P.τ i t = ev P.τ (th i δ) := by
  induction t with
  | par c => left; exact ⟨rfl, rfl⟩
  | add s r ihs ihr =>
    rw [top_add, star_add]
    rcases ihs with ⟨hs1, hs2⟩ | ⟨δ, hs1, hs2, hs3⟩ <;> rcases ihr with ⟨hr1, hr2⟩ | ⟨δ', hr1, hr2, hr3⟩
    · left; rw [hs1, hr1, hs2, hr2]; exact ⟨rfl, max_self 0⟩
    · right; refine ⟨δ', ?_, ?_, ?_⟩
      · rw [hs1, hr1]; rfl
      · simp only [Ki, List.mem_append]; exact Or.inr hr2
      · rw [hs2, hr3]; exact max_eq_right zero_le
    · right; refine ⟨δ, ?_, ?_, ?_⟩
      · rw [hs1, hr1]; rfl
      · simp only [Ki, List.mem_append]; exact Or.inl hs2
      · rw [hr2, hs3]; exact max_eq_left zero_le
    · rw [hs1, hr1, hs3, hr3]
      by_cases hle : ev P.τ (th i δ') ≤ ev P.τ (th i δ)
      · right; refine ⟨δ, ?_, ?_, max_eq_left hle⟩
        · simp only [omax]; rw [if_pos hle]
        · simp only [Ki, List.mem_append]; exact Or.inl hs2
      · right; refine ⟨δ', ?_, ?_, max_eq_right (not_le.1 hle).le⟩
        · simp only [omax]; rw [if_neg hle]
        · simp only [Ki, List.mem_append]; exact Or.inr hr2
  | th j u ih =>
    rw [top_th]
    by_cases h1 : j < i
    · left; rw [if_pos h1]; refine ⟨rfl, ?_⟩
      unfold Tm.star; simp [Ki, h1]
    · by_cases h2 : j = i
      · subst h2
        right; refine ⟨u, ?_, ?_, ?_⟩
        · simp
        · simp [Ki]
        · unfold Tm.star; simp [Ki]
      · rw [if_neg h1, if_neg h2]
        have hK : Ki i (th j u) = Ki i u := by simp [Ki, h1, h2]
        have hS : Tm.star P.τ i (th j u) = Tm.star P.τ i u := by unfold Tm.star; rw [hK]
        rw [hS]
        rcases ih with h | ⟨δ, e1, e2, e3⟩
        · left; exact h
        · right; exact ⟨δ, e1, by rw [hK]; exact e2, e3⟩

theorem cof_top_le (i : ℕ) (t : Tm) : cof (P.top i t) ≤ P.a i t := le_self_add

theorem code_le_a (i : ℕ) (t : Tm) : P.code i (ω ^ P.B t) ≤ P.a i t := le_add_self

/-- `aᵢ(t) < Ω_ω` for normal `t`. -/
theorem a_lt_Om_omega (H : P.Hyp) (i : ℕ) : ∀ (n : ℕ) (t : Tm), size t ≤ n → NF P.τ t →
    P.a i t < Om (ω : Ordinal.{0}) := by
  intro n
  induction n with
  | zero => intro t h; exact absurd (size_pos t) (by omega)
  | succ n ih =>
    intro t hs ht
    have hc : P.code i (ω ^ P.B t) < Om (ω : Ordinal.{0}) := by
      have he : ω ^ P.B t < Om (ω : Ordinal.{0}) := by
        have := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero) _
          (B_lt_Om_omega H ht)
        rwa [veblen_zero_apply] at this
      by_cases hm : i = 0 ∧ P.md = true
      · unfold code; rw [if_pos hm]
        exact (psi_lt (kap_InR P.S 1) _).trans (kap_lt_Om_omega 1)
      · rw [code_ne _ _ _ hm]; exact he
    rcases P.top_spec i t with ⟨h1, _⟩ | ⟨δ, h1, h2, _⟩
    · unfold a; rw [h1]; simpa [cof] using hc
    · unfold a; rw [h1]
      obtain ⟨_, -, hsz⟩ := Ki_shape h2
      have hδ := ih δ (by simp [size] at hsz; omega) (NF.th_arg (NF.Ki ht h2))
      exact Om_omega_principal (Om_omega_principal hδ (lt_of_lt_of_le one_lt_omega0
        (omega0_lt_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).le)) hc

/-! ## The generation lemma -/

/-- **Generation.**  With `b` and `μ` such that the arguments of all parts of level `≥ L` are below `b`,
`B(t)` and those arguments lie in `Cl(b, μ)`. -/
theorem gen (_H : P.Hyp) (L : ℕ) (b μ : Ordinal.{0}) (hτμ : P.τ ≤ μ)
    (hlow : ∀ k < L, kap k ≤ μ) (hX : ∀ k, L ≤ k → P.X k ∈ P.S.CSet b μ) :
    ∀ {t : Tm}, NF P.τ t → (∀ p ∈ Kst L t, P.X p.1 + P.a p.1 p.2 < b) →
      (∀ p ∈ Kst L t, p.1 = 0 → P.md = true → ω ^ P.B p.2 < b) →
      P.B t ∈ P.S.CSet b μ ∧ ∀ p ∈ Kst L t, P.a p.1 p.2 ∈ P.S.CSet b μ := by
  intro t ht
  induction ht with
  | @cpar c hc =>
    intro _ _
    refine ⟨CSet.of_lt (lt_of_lt_of_le hc hτμ), ?_⟩
    intro p hp; simp [Kst] at hp
  | @cth j u hu hdm ih =>
    intro hb hcode
    by_cases hjL : j < L
    · refine ⟨CSet.of_lt (lt_of_lt_of_le (P.B_th_bounds j u).2 (hlow j hjL)), ?_⟩
      intro p hp; simp [Kst, hjL] at hp
    have hK : Kst L (th j u) = (j, u) :: Kst L u := by simp [Kst, hjL]
    rw [hK] at hb hcode
    obtain ⟨ihB, iha⟩ := ih (fun p hp => hb p (List.mem_cons_of_mem _ hp))
      (fun p hp => hcode p (List.mem_cons_of_mem _ hp))
    have hau : P.a j u ∈ P.S.CSet b μ := by
      unfold a
      refine CSet.add_mem ?_ ?_
      · rcases P.top_spec j u with ⟨h1, _⟩ | ⟨δ, h1, h2, _⟩
        · rw [h1]; exact CSet.zero_mem _ _
        · rw [h1]
          exact CSet.succ_mem (iha (j, δ) (Ki_sub_Kst (not_lt.1 hjL) h2))
      · have hw : ω ^ P.B u ∈ P.S.CSet b μ := by
          have := CSet.phi_mem (CSet.zero_mem (S := P.S) b μ) ihB
          rwa [veblen_zero_apply] at this
        by_cases hm : j = 0 ∧ P.md = true
        · unfold code; rw [if_pos hm]
          exact CSet.psi_mem (hcode (j, u) List.mem_cons_self hm.1 hm.2) (kap_InR P.S 1)
            (kap_mem 1 _ _) hw
        · rw [code_ne _ _ _ hm]; exact hw
    refine ⟨?_, ?_⟩
    · rw [B_th]
      exact CSet.psi_mem (hb (j, u) List.mem_cons_self) (kap_InR P.S j) (kap_mem j _ _)
        (CSet.add_mem (hX j (not_lt.1 hjL)) hau)
    · rw [hK]
      intro p hp
      rcases List.mem_cons.1 hp with h | h
      · subst h; exact hau
      · exact iha p h
  | @cadd j u r h1 h2 _ _ ih1 ih2 =>
    intro hb hcode
    simp only [Kst, List.mem_append] at hb hcode
    obtain ⟨g1, k1⟩ := ih1 (fun p hp => hb p (Or.inl hp)) (fun p hp => hcode p (Or.inl hp))
    obtain ⟨g2, k2⟩ := ih2 (fun p hp => hb p (Or.inr hp)) (fun p hp => hcode p (Or.inr hp))
    refine ⟨by rw [B_add]; exact CSet.add_mem g1 g2, ?_⟩
    intro p hp
    simp only [Kst, List.mem_append] at hp
    rcases hp with hp | hp
    · exact k1 p hp
    · exact k2 p hp

end BP

end Googology.Trans.PoR.InaccPsi.R2.Br
