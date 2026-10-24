import Googology.Trans.PoR.InaccPsi.R2.TdLev

/-!
# Derivations with the hull-limit rule (members per hull element and per own pair)

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

At a limit code level `c` the members `φ(c', ·)`, `c' < c` codes, are cofinal in `φ(c, ·)` only among the hull
elements (`Td.tdHull_levDec`; below `Ω₁` the hull is `ρ_λ`), so the family-limit rule `Ta.TaDer.flim` (cofinal
among ALL ordinals) does not apply.  `TdDer S λ Ow E Ê` has the rules of `Ta.TaDer` and
* `hlim` (**the hull-limit rule**): own data `Sc.ScOwP Ow E Ê`, `E < G3`, `Ê < G1`, members `e_i < E`, `ê_i < Ê`
  derived with own predicates `Ow_i`; for every own pair `(b, X₀)` and **every hull element** `y < W^E` some member
  own at `(b, X₀)` has `y < W^{e_i}`, and for every `z < Ω^Ê` some member own at `(b, X₀)` has `z < Ω^{ê_i}`
  (exactly the hypotheses of `St.stLevLimH`).

* `tdDer_of_ta` (every `Ta.TaDer` derivation is a `TdDer` derivation), `tdDer_cast`;
* `tdTh_lim` (`Θ c` is a limit for a limit `c`), `tdTh_levCof` (**THE IMAGE COFINALITY AT A LIMIT CODE LEVEL**:
  every `z < φ(Θ c, w + 1)` is below `φ(Θ c', φ(Θ c, w) + 1)` for a code `c' < c`; with `Td.tdHull_levDec` on the
  value side these are the two cofinality conditions of `hlim` for the members `φ(c', ·)`);
* `tdDer_sound` (**SOUNDNESS: every derivation gives `Sc.ScLev Ow E Ê` and `Sc.ScOwP Ow E Ê`**).

No new axiom.  New definition: `TdDer`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **A derivation of the exponent `E` (image `Ê`, own predicate `Ow`), with the hull-limit rule.** -/
inductive TdDer (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    (Ordinal.{0} → Ordinal.{0} → Prop) → Ordinal.{0} → Ordinal.{0} → Prop
  | code {E : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) →
      TdDer S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E)
  | succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      TdDer S l Ow E Eh → TdDer S l Ow (E + 1) (Eh + 1)
  | om {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
        TdDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
          (gh (gxTh (upsilon l) (ldAtR S l) ζ))) →
      TdDer S l Ow gs ghs
  | lim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs η : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      GxCl (upsilon l) (ldAtR S l) η → η < Om (1 + 1) → IsSuccLimit η →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < η →
        TdDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ + 1 < scSq S (fun z => leWe (g z)) X0 b j) (g (ζ + 1))
          (gh (gxTh (upsilon l) (ldAtR S l) (ζ + 1)))) →
      TdDer S l (fun b X0 => Ow b X0 ∧ ∃ j, η < scSq S (fun z => leWe (g z)) X0 b j) (g η)
        (gh (gxTh (upsilon l) (ldAtR S l) η))
  | weaken {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      TdDer S l Ow E Eh → (∀ b X0, Ow' b X0 → Ow b X0) →
      (∀ b β X0 X0', Ow' b X0 → b ≤ β → X0 ≤ X0' → Ow' β X0') → TdDer S l Ow' E Eh
  | hlim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} {ι : Type 1} {e eh : ι → Ordinal.{0}}
      {Ow' : ι → Ordinal.{0} → Ordinal.{0} → Prop} :
      ScOwP S l Ow E Eh → E < S.psi 0 (Om (1 + 1 + 1)) → Eh < S.psi 0 (Om (1 + 1)) →
      (∀ i, TdDer S l (Ow' i) (e i) (eh i)) → (∀ i, e i < E) → (∀ i, eh i < Eh) →
      (∀ b X0, Ow b X0 → ∀ y, y ∈ cdHull S l → y < leWe E → ∃ i, Ow' i b X0 ∧ y < leWe (e i)) →
      (∀ b X0, Ow b X0 → ∀ z, z < leOe Eh → ∃ i, Ow' i b X0 ∧ z < leOe (eh i)) →
      TdDer S l Ow E Eh

theorem tdDer_cast {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {x x' y y' : Ordinal.{0}}
    (h : TdDer S l Ow x y) (hx : x = x') (hy : y = y') : TdDer S l Ow x' y' := hx ▸ hy ▸ h

/-- **Every `Ta.TaDer` derivation is a `TdDer` derivation** (`flim` is the case of `hlim` with the members
cofinal among all ordinals and own wherever `Ow` holds). -/
theorem tdDer_of_ta {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}}
    (h : TaDer S l Ow E Eh) : TdDer S l Ow E Eh := by
  induction h with
  | code hE h1 hEW => exact TdDer.code hE h1 hEW
  | succ _ IH => exact TdDer.succ IH
  | om hshp hmono _ IH => exact TdDer.om hshp hmono IH
  | lim hshp hmono hη hηW hlim _ IH => exact TdDer.lim hshp hmono hη hηW hlim IH
  | weaken _ himp hmono IH => exact TdDer.weaken IH himp hmono
  | flim hP hEG hEhG _ himp hek hehk hcof hcofh IH =>
    refine TdDer.hlim hP hEG hEhG IH hek hehk (fun b X0 hO y _ hy => ?_) (fun b X0 hO z hz => ?_)
    · obtain ⟨i, hi⟩ := hcof y hy; exact ⟨i, himp i b X0 hO, hi⟩
    · obtain ⟨i, hi⟩ := hcofh z hz; exact ⟨i, himp i b X0 hO, hi⟩

/-! ## The cofinality of the members at a limit code level -/

section Cof

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z)

include hZ

/-- **`Θ c` is a limit for a limit `c`** (`Θ` the order type of the codes below). -/
theorem tdTh_lim {c : Ordinal.{0}} (hc : IsSuccLimit c) : IsSuccLimit (gxTh Z At c) := by
  have h0 : gxTh Z At 0 < gxTh Z At c := gxTh_lt (GxCl.zero hZ.1) hc.bot_lt
  rw [gxTh_zero] at h0
  refine ⟨not_isMin_iff.2 ⟨0, h0⟩, fun v hv => ?_⟩
  obtain ⟨c', hc', hc'c, e⟩ := gxTh_onto hv.lt
  have hc1 : GxCl Z At (c' + 1) := GxCl.add hc' (GxCl.small (gg_one_lt_of_SC hZ))
  have h1 : gxTh Z At c' < gxTh Z At (c' + 1) := gxTh_lt hc' (lt_add_one c')
  have h2 : gxTh Z At (c' + 1) < gxTh Z At c := gxTh_lt hc1 (hc.add_one_lt hc'c)
  rw [e] at h1
  exact hv.2 h1 h2

/-- **THE IMAGE COFINALITY AT A LIMIT CODE LEVEL**: `z < φ(Θ c, w + 1)` is below `φ(Θ c', φ(Θ c, w) + 1)` for a
code `c' < c`. -/
theorem tdTh_levCof {c w z : Ordinal.{0}} (hc : IsSuccLimit c) (hz : z < veblen (gxTh Z At c) (w + 1)) :
    ∃ c', GxCl Z At c' ∧ c' < c ∧ z < veblen (gxTh Z At c') (veblen (gxTh Z At c) w + 1) := by
  obtain ⟨a', ha', hza⟩ := taVeb_lim_cof (tdTh_lim hZ hc) hz
  obtain ⟨c', hc', hc'c, e⟩ := gxTh_onto ha'
  exact ⟨c', hc', hc'c, by rw [e]; exact hza⟩

end Cof

section Sound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **SOUNDNESS: every derivation gives the level statement and the data of its own predicate.** -/
theorem tdDer_sound {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : TdDer S l Ow E Eh) :
    ScLev S l Ow E Eh ∧ ScOwP S l Ow E Eh := by
  induction h with
  | code hE h1 hEW => exact ⟨scLev_code_iff.2 (rwLevC_all hl hX _ hE h1 hEW), scOwP_code hl hX h1 hE hEW⟩
  | succ _ IH => exact ⟨scLev_succ hl hX IH.2 IH.1 (fun _ _ h => h), scOwP_succ IH.2⟩
  | om hshp hmono _ IH =>
    exact ⟨scLev_om hl hX hshp (fun b β X0 hO hb => hmono b β X0 X0 hO hb le_rfl)
      (fun ζ hζ h1 hζW => (IH ζ hζ h1 hζW).1), scOwP_om hshp hmono⟩
  | lim hshp hmono hη hηW hlim _ IH =>
    exact ⟨scLev_lim hl hX hshp hmono hη hηW hlim (fun ζ hζ hζη => (IH ζ hζ hζη).1),
      scOwP_mem hshp hmono hη (rvLim_one_lt hlim).le⟩
  | weaken _ himp hmono IH =>
    exact ⟨fun b X0 Xh0 hoff hd hG3 hG hO => IH.1 b X0 Xh0 hoff hd hG3 hG (himp b X0 hO),
      ⟨fun b X0 hO => IH.2.dat b X0 (himp b X0 hO), hmono⟩⟩
  | hlim hP hEG hEhG _ hek hehk hcof hcofh IH =>
    refine ⟨St.stLevLimH hl hX hP hEG hEhG (fun b X0 hO y hyH hy => ?_) (fun b X0 hO z hz => ?_), hP⟩
    · obtain ⟨i, hOi, hi⟩ := hcof b X0 hO y hyH hy
      exact ⟨_, _, _, (IH i).2, (IH i).1, hOi, hek i, hehk i, hi⟩
    · obtain ⟨i, hOi, hi⟩ := hcofh b X0 hO z hz
      exact ⟨_, _, _, (IH i).2, (IH i).1, hOi, hek i, hehk i, hi⟩

end Sound

end Googology.Trans.PoR.InaccPsi.R2.Td
