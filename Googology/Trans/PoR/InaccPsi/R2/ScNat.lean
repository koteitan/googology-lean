import Googology.Trans.PoR.InaccPsi.R2.ScAddW

/-!
# The linear step on derived exponents, iterated: `E₀ ↦ E₀ + W^n` and `W^n` for every `n`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`.

`ScAddF S λ F F̂` (**the family step at `F`**): every derived `E₀` (own predicate `Ow`, image `Ê₀`) with
`W^F ∣ E₀` gives the derived `E₀ + W^F` (image `Ê₀ + Ω^{F̂}`, the same `Ow`).

* `scDer_linCore` (**one lemma for every linear shape**: if the members `g ζ` satisfy
  `g(ζ+1) = g ζ + W^F`, `ĝ(v+1) = ĝ v + Ω^{F̂}`, `W^F ∣ g ζ`, the family step at `F` holds and `g 1` is derived,
  then the top `g*` of the shape is derived);
* `scNat_mem`, `scNat_cl`, `scAddF_zero` (`E₀ ↦ E₀ + 1`), `scAddF_succ` (**the family step at `n` gives the step at
  `n+1`**), `scAddF_nat` (every `n`), `scDer_Wn` (**`W^n` is derived for every `n ≥ 1`**, image `Ω₁^n`, own
  predicate `⊤`), `scLev_Wn` (**the top at `W^{Ω₂^n}` over every offset and base bound**).

No new axiom.  New definition: `ScAddF`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

/-- **The family step at `F`.** -/
def ScAddF (S : InaccSeq.{0}) (l F Fh : Ordinal.{0}) : Prop :=
  ∀ (Ow : Ordinal.{0} → Ordinal.{0} → Prop) (E0 Eh0 : Ordinal.{0}), ScDer S l Ow E0 Eh0 → leWe F ∣ E0 →
    ScDer S l Ow (E0 + leWe F) (Eh0 + leOe Fh)

theorem scNat_mem (a c : Ordinal.{0}) : ∀ n : ℕ, ((n : ℕ) : Ordinal.{0}) ∈ S.CSet a c
  | 0 => by rw [Nat.cast_zero]; exact CSet.zero_mem _ _
  | n + 1 => by rw [Nat.cast_succ]; exact CSet.succ_mem (scNat_mem a c n)

theorem scNat_cl {κ Q : Ordinal.{0}} (hQ : SC Q) : ∀ n : ℕ, LeCl κ Q ((n : ℕ) : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero]; exact LeCl.zero hQ.1
  | n + 1 => by rw [Nat.cast_succ]; exact LeCl.add (scNat_cl hQ n) (LeCl.small (gg_one_lt_of_SC hQ))

section Lin

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **One lemma for every linear shape.** -/
theorem scDer_linCore {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}}
    {gs ghs F Fh : Ordinal.{0}}
    (hshp : ∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
      (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)))
    (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') (hAdd : ScAddF S l F Fh)
    (hg : ∀ ζ, g (ζ + 1) = g ζ + leWe F) (hgh : ∀ v, gh (v + 1) = gh v + leOe Fh) (hdv : ∀ ζ, leWe F ∣ g ζ)
    (hD1 : ScDer S l Ow (g 1) (gh 1)) : ScDer S l Ow gs ghs := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hGmo : ∀ b X0, Ow b X0 → Monotone (fun z => leWe (g z)) :=
    fun b X0 hO a c h => leWe_mono ((hshp b X0 hO).st.monotone h)
  have hmo : ∀ ζ, ∀ b β X0 X0', (Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) → b ≤ β → X0 ≤ X0' →
      (Ow β X0' ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0' β j) := fun ζ b β X0 X0' ⟨hO, j, hj⟩ hb hXX =>
    ⟨hmono _ _ _ _ hO hb hXX, j, hj.trans_le ((scSq_mono_base (hGmo b X0 hO) hb j).trans
      (scSq_mono_off (hGmo b X0 hO) hXX j))⟩
  have hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
      ScDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
        (gh (gxTh (upsilon l) (ldAtR S l) ζ)) := by
    intro ζ
    induction ζ using WellFoundedLT.induction with
    | ind ζ IH =>
    intro hζ h1 hζW
    rcases zero_or_succ_or_isSuccLimit ζ with h0 | ⟨ζ0, hζ0⟩ | hlim
    · subst h0; exact absurd h1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hζ0
      subst hζ0
      have hζ0c := rqCode_pred hl hX hζ hζW
      rcases eq_or_ne ζ0 0 with rfl | h00
      · rw [zero_add, gxTh_small (gg_one_lt_of_SC hρSC).le]
        exact ScDer.weaken hD1 (fun _ _ h => h.1) (hmo 1)
      · have h10 : 1 ≤ ζ0 := Order.one_le_iff_ne_zero.2 h00
        rw [hg, rqTh_succ hl hX hζ0c, hgh]
        exact ScDer.weaken (hAdd _ _ _ (IH ζ0 (lt_add_one ζ0) hζ0c h10 ((lt_add_one ζ0).trans hζW)) (hdv ζ0))
          (fun _ _ ⟨hO, j, hj⟩ => ⟨hO, j, (lt_add_one ζ0).trans hj⟩) (hmo (ζ0 + 1))
    · exact ScDer.lim hshp hmono hζ hζW hlim fun c hc hcζ =>
        IH (c + 1) (hlim.succ_lt hcζ) (rqCode_succ hl hX hc ((hlim.succ_lt hcζ).trans hζW)) le_add_self
          ((hlim.succ_lt hcζ).trans hζW)
  exact ScDer.om hshp hmono hmem

omit hl hX in
/-- **`E₀ ↦ E₀ + 1`.** -/
theorem scAddF_zero : ScAddF S l 0 0 := by
  intro Ow E0 Eh0 hD _
  rw [leWe_zero, leOe_zero]; exact ScDer.succ hD

/-- **The family step at `n` gives the step at `n + 1`.** -/
theorem scAddF_succ (n : ℕ) (hA : ScAddF S l (n : ℕ) (n : ℕ)) : ScAddF S l ((n : ℕ) + 1) ((n : ℕ) + 1) := by
  intro Ow E0 Eh0 hD hdv
  obtain ⟨-, hP⟩ := scDer_sound hl hX hD
  have hdvF : leWe ((n : ℕ) : Ordinal.{0}) ∣ E0 := (leWe_dvd le_self_add).trans hdv
  refine scDer_linCore hl hX (g := fun z => E0 + leWe (n : ℕ) * z) (gh := fun v => Eh0 + leOe (n : ℕ) * v)
    (F := (n : ℕ)) (Fh := (n : ℕ)) ?_ hP.mono hA (fun ζ => by simp only [mul_add_one, add_assoc])
    (fun v => by simp only [mul_add_one, add_assoc]) (fun ζ => dvd_add hdvF (dvd_mul_right _ _)) ?_
  · intro b X0 hO
    have hd := hP.dat b X0 hO
    have hY : S.psi (b + leWe (X0 + leWe E0)) (Om (1 + 1)) ≤
        leTe S (X0 + leWe ((fun z => E0 + leWe (n : ℕ) * z) 1)) b := scTop_mono le_rfl le_rfl le_self_add
    have hlin := scShp_lin hl hX (F := (n : ℕ)) (Fh := (n : ℕ)) (bot := leTe S (X0 + leWe
      ((fun z => E0 + leWe (n : ℕ) * z) 1)) b) (both := gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe
      ((fun z => E0 + leWe (n : ℕ) * z) 1)) b)) (scNat_mem _ _ n) (scNat_mem _ _ n) (scNat_mem _ _ n)
      (fun Q hQ _ => scNat_cl hQ n) (fun Q hQ _ => scNat_cl hQ n)
    exact scShp_pre hl hX hlin hd.hull (CSet_mono le_rfl hY hd.mem) (CSet_mono le_rfl (gxTh_mono hY) hd.memh)
      (fun Q hQ hc => hd.cl Q hQ (hY.trans hc)) (fun Q hQ hc => hd.clh Q hQ ((gxTh_mono hY).trans hc))
      (k := Om (1 + 1) * ((n : ℕ) + 1)) rfl hdv
  · simp only [mul_one]; exact hA Ow E0 Eh0 hD hdvF

/-- **The family step at every `n`.** -/
theorem scAddF_nat : ∀ n : ℕ, ScAddF S l (n : ℕ) (n : ℕ)
  | 0 => by rw [Nat.cast_zero]; exact scAddF_zero
  | n + 1 => by rw [Nat.cast_succ]; exact scAddF_succ hl hX n (scAddF_nat n)

/-- **`W^n` is derived for every `n ≥ 1`** (image `Ω₁^n`, own predicate `⊤`). -/
theorem scDer_Wn : ∀ n : ℕ, ScDer S l (fun _ _ => True) (leWe ((n : ℕ) + 1)) (leOe ((n : ℕ) + 1))
  | 0 => by rw [Nat.cast_zero, zero_add, leWe_one, leOe_one]; exact scDer_W hl hX
  | n + 1 => by
    have IH := scDer_Wn n
    have hshp : ∀ b X0 : Ordinal.{0}, (fun _ _ : Ordinal.{0} => True) b X0 →
        ScShp S l (fun z => leWe ((n : ℕ) + 1) * z) (fun v => leOe ((n : ℕ) + 1) * v)
          (leWe ((n : ℕ) + 1 + 1)) (leOe ((n : ℕ) + 1 + 1))
          (leTe S (X0 + leWe ((fun z => leWe ((n : ℕ) + 1) * z) 1)) b)
          (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => leWe ((n : ℕ) + 1) * z) 1)) b)) := by
      intro b X0 _
      have h := scShp_lin hl hX (F := ((n + 1 : ℕ) : Ordinal.{0})) (Fh := ((n + 1 : ℕ) : Ordinal.{0}))
        (bot := leTe S (X0 + leWe ((fun z => leWe ((n : ℕ) + 1) * z) 1)) b)
        (both := gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => leWe ((n : ℕ) + 1) * z) 1)) b))
        (scNat_mem _ _ (n + 1)) (scNat_mem _ _ (n + 1)) (scNat_mem _ _ (n + 1))
        (fun Q hQ _ => scNat_cl hQ (n + 1)) (fun Q hQ _ => scNat_cl hQ (n + 1))
      simpa only [Nat.cast_succ] using h
    have hA := scAddF_nat hl hX (n + 1)
    rw [Nat.cast_succ] at hA
    rw [Nat.cast_succ]
    refine scDer_linCore hl hX hshp (fun _ _ _ _ _ _ _ => trivial) hA
      (fun ζ => by simp only [mul_add_one]) (fun v => by simp only [mul_add_one])
      (fun ζ => dvd_mul_right _ _) ?_
    simp only [mul_one]; exact IH

/-- **The top at `W^{Ω₂^n}` over every offset and base bound** (image `Ω^{Ω₁^n}`), every `n ≥ 1`. -/
theorem scLev_Wn (n : ℕ) : ScLev S l (fun _ _ => True) (leWe ((n : ℕ) + 1)) (leOe ((n : ℕ) + 1)) :=
  (scDer_sound hl hX (scDer_Wn hl hX n)).1

end Lin

end Googology.Trans.PoR.InaccPsi.R2.Sc
