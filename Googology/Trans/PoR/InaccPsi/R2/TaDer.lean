import Googology.Trans.PoR.InaccPsi.R2.TaCtx

/-!
# Derivations with the family-limit rule

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

`TaDer S λ Ow E Ê` (**a derivation**): the rules of `Sc.ScDer` (`code`, `succ`, `om`, `lim`, `weaken`) with members
derived in `TaDer`, and
* `flim` (**the family-limit rule**): own data `Sc.ScOwP Ow E Ê`, `E < G3`, `Ê < G1`, members `e_i < E`, `ê_i < Ê`
  (`i` ranging over **any** index type, e.g. the Veblen levels `a' < a` of a limit level `a`) derived with own
  predicates `Ow_i` implied by `Ow`, `W^{e_i}` cofinal in `W^E` and `Ω^{ê_i}` cofinal in `Ω^Ê` give `E`
  (`St.stLevLimH`; `Sw.SwDer.wlim` is the case of an `ω`-sequence).

* `taDer_sound` (**SOUNDNESS: every derivation gives the level statement `Sc.ScLev Ow E Ê` and the own data**).

No new axiom.  New definition: `TaDer`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **A derivation of the exponent `E` (image `Ê`, own predicate `Ow`), with the family-limit rule.** -/
inductive TaDer (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    (Ordinal.{0} → Ordinal.{0} → Prop) → Ordinal.{0} → Ordinal.{0} → Prop
  | code {E : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) →
      TaDer S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E)
  | succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      TaDer S l Ow E Eh → TaDer S l Ow (E + 1) (Eh + 1)
  | om {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
        TaDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
          (gh (gxTh (upsilon l) (ldAtR S l) ζ))) →
      TaDer S l Ow gs ghs
  | lim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs η : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      GxCl (upsilon l) (ldAtR S l) η → η < Om (1 + 1) → IsSuccLimit η →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < η →
        TaDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ + 1 < scSq S (fun z => leWe (g z)) X0 b j) (g (ζ + 1))
          (gh (gxTh (upsilon l) (ldAtR S l) (ζ + 1)))) →
      TaDer S l (fun b X0 => Ow b X0 ∧ ∃ j, η < scSq S (fun z => leWe (g z)) X0 b j) (g η)
        (gh (gxTh (upsilon l) (ldAtR S l) η))
  | weaken {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      TaDer S l Ow E Eh → (∀ b X0, Ow' b X0 → Ow b X0) →
      (∀ b β X0 X0', Ow' b X0 → b ≤ β → X0 ≤ X0' → Ow' β X0') → TaDer S l Ow' E Eh
  | flim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} {ι : Type 1} {e eh : ι → Ordinal.{0}}
      {Ow' : ι → Ordinal.{0} → Ordinal.{0} → Prop} :
      ScOwP S l Ow E Eh → E < S.psi 0 (Om (1 + 1 + 1)) → Eh < S.psi 0 (Om (1 + 1)) →
      (∀ i, TaDer S l (Ow' i) (e i) (eh i)) → (∀ i b X0, Ow b X0 → Ow' i b X0) →
      (∀ i, e i < E) → (∀ i, eh i < Eh) →
      (∀ y, y < leWe E → ∃ i, y < leWe (e i)) → (∀ z, z < leOe Eh → ∃ i, z < leOe (eh i)) →
      TaDer S l Ow E Eh

theorem taDer_cast {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {x x' y y' : Ordinal.{0}}
    (h : TaDer S l Ow x y) (hx : x = x') (hy : y = y') : TaDer S l Ow x' y' := hx ▸ hy ▸ h

section Sound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **SOUNDNESS: every derivation gives the level statement and the data of its own predicate.** -/
theorem taDer_sound {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : TaDer S l Ow E Eh) :
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
  | flim hP hEG hEhG _ himp hek hehk hcof hcofh IH =>
    refine ⟨St.stLevLimH hl hX hP hEG hEhG (fun b X0 hO y _ hy => ?_) (fun b X0 hO z hz => ?_), hP⟩
    · obtain ⟨i, hi⟩ := hcof y hy
      exact ⟨_, _, _, (IH i).2, (IH i).1, himp i b X0 hO, hek i, hehk i, hi⟩
    · obtain ⟨i, hi⟩ := hcofh z hz
      exact ⟨_, _, _, (IH i).2, (IH i).1, himp i b X0 hO, hek i, hehk i, hi⟩

end Sound

end Googology.Trans.PoR.InaccPsi.R2.Ta
