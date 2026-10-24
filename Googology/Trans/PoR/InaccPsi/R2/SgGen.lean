import Googology.Trans.PoR.InaccPsi.R2.SgShp

/-!
# Every own exponent term is derived

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `SQ_j(g) = Sc.scSq S (z ↦ W^{g z}) X₀ b j`.

One induction on the value `v`, inside it on the exponent term and the context:
* `K(R̄ + 1)` (`SgGenAt`, first part): `hole`: `1` is a code, `Q + 1` is a successor of the derived `Q`;
  `pfx K Q'`: concatenate `Q' ⊕ Q`; `lft K`: `K(W^{Q+1})` is the top of the path shape `ζ ↦ K(W^Q·ζ)` whose
  members are derived at smaller values (`Sc.ScDer.om`).
* `K(W^R·c)` (second part): `c` a limit code: the path shape `ζ ↦ K(W^R·ζ)` at `c` (`Sc.ScDer.lim`, members
  `K(W^R·(ζ+1))` at smaller values); `c = d + 1 ≥ 2`: the context `pfx K (W^R·d)` and `c = 1`; `c = 1`:
  `R = zero` is the first part, `R = P' + W^{R'}·c'` is the context `pfx (lft K) P'` and the term `R'`.

* `sgGen_all` (**THE GENERATION: at every value both parts hold, for every own predicate `Ow` (monotone in the
  base and the offset) that implies the own predicates of the context and the term**);
* `sgDer_term` (**every well-formed term `t` with `val t ≥ 1` is derived**, own predicate `SgOwn id t`,
  image `sgI t`), `sgLev_term` (**the level statement `Sc.ScLev` at every such term**: the top law
  `Θ(ψ_{Ω₂}(β + W^{X₀ + W^{val t}})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{sgI t}})` over every offset and base bound
  whose own predicate holds).

No new axiom.  New definition: `SgGenAt` (a statement name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

/-- **The generation statement at the value `v`.** -/
def SgGenAt (S : InaccSeq.{0}) (l v : Ordinal.{0}) : Prop :=
  (∀ (K : SgC) (Q : SgT), SgWFC S l K → SgWF S l Q → sgE K (sgV Q + 1) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → SgOwnC S b X0 K ∧ SgOwn S b X0 (sgE K) Q) →
    ScDer S l Ow (sgE K (sgV Q + 1)) (sgEh S l K (sgI S l Q + 1))) ∧
  (∀ (K : SgC) (R : SgT) (c : Ordinal.{0}), SgWFC S l K → SgWF S l R → GxCl (upsilon l) (ldAtR S l) c →
    1 ≤ c → c < Om (1 + 1) → sgE K (leWe (sgV R) * c) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → SgOwnC S b X0 K ∧ SgOwn S b X0 (fun r => sgE K (leWe r)) R ∧
      SgLimC S (fun z => sgE K (leWe (sgV R) * z)) c b X0) →
    ScDer S l Ow (sgE K (leWe (sgV R) * c)) (sgEh S l K (leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c)))

variable {S : InaccSeq.{0}}

theorem sgDer_cast {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {x x' y y' : Ordinal.{0}}
    (h : ScDer S l Ow x y) (hx : x = x') (hy : y = y') : ScDer S l Ow x' y' := hx ▸ hy ▸ h

theorem sgLimC_one {G : Ordinal.{0} → Ordinal.{0}} {b X0 : Ordinal.{0}} : SgLimC S G 1 b X0 :=
  fun η hη hlim => absurd hη (not_le.2 (rvLim_one_lt hlim))

section Gen

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE GENERATION at every value.** -/
theorem sgGen_all : ∀ v, SgGenAt S l v := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  -- the first part, by induction on the context
  have hA : ∀ (K : SgC) (Q : SgT), SgWFC S l K → SgWF S l Q → sgE K (sgV Q + 1) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → SgOwnC S b X0 K ∧ SgOwn S b X0 (sgE K) Q) →
      ScDer S l Ow (sgE K (sgV Q + 1)) (sgEh S l K (sgI S l Q + 1)) := by
    intro K
    induction K with
    | hole =>
      intro Q hKw hQw hv Ow hmono hown
      cases Q with
      | zero =>
        have h1 : ScDer S l (fun b X0 => ∃ j, (1 : Ordinal.{0}) < rwEX S X0 b j) 1 (gxTh (upsilon l) (ldAtR S l) 1) :=
          ScDer.code (GxCl.small (gg_one_lt_of_SC hρSC)) le_rfl (gg_one_lt_of_SC ldOm2_SC)
        refine sgDer_cast (ScDer.weaken h1 (fun _ _ _ => ⟨0, gg_one_lt_of_SC Ph.ph_SC_Om1⟩) hmono) ?_ ?_
        · show (1 : Ordinal.{0}) = 0 + 1; rw [zero_add]
        · show gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [zero_add, hΘ1]
      | term P R c =>
        obtain ⟨hPw, hRw, hc, hc1, hcW⟩ := hQw
        have hlt : sgV (SgT.term P R c) < v := by rw [← hv]; exact lt_add_one _
        have hD := (IH _ hlt).2 (SgC.pfx SgC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl Ow hmono
          (fun b X0 h => by
            obtain ⟨-, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨trivial, hP⟩, hR, hcl⟩)
        exact ScDer.succ hD
    | pfx K Q' IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have e1 : sgV (sgCat Q' Q) + 1 = sgV Q' + (sgV Q + 1) := by rw [sgV_cat, add_assoc]
      have e2 : sgI S l (sgCat Q' Q) + 1 = sgI S l Q' + (sgI S l Q + 1) := by rw [sgI_cat, add_assoc]
      have hD := IHK (sgCat Q' Q) hKw.1 (sgWF_cat hKw.2 Q hQw) (by rw [e1]; exact hv) Ow hmono
        (fun b X0 h => by
          obtain ⟨⟨hK, hQ'⟩, hQ⟩ := hown b X0 h
          exact ⟨hK, sgOwn_cat Q (sgE K) (sgE_mono K) hQ' hQ⟩)
      exact sgDer_cast hD (by rw [e1]; rfl) (by rw [e2]; rfl)
    | lft K IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have hGm : Monotone (fun z => leWe (sgE K (leWe (sgV Q) * z))) :=
        fun _ _ h => leWe_mono (sgE_mono K (leMulWe_mono h))
      refine ScDer.om (g := fun z => sgE K (leWe (sgV Q) * z))
        (gh := fun v => sgEh S l K (leOe (sgI S l Q) * v))
        (fun b X0 h => sgShp_path hl hX hKw hQw (hown b X0 h).1 (hown b X0 h).2) hmono ?_
      intro ζ hζ h1 hζW
      have hlt : sgE K (leWe (sgV Q) * ζ) < v := by
        rw [← hv]; exact sgE_strictMono K (rvWe_lt_succ hζW)
      exact (IH _ hlt).2 K Q ζ hKw hQw hζ h1 hζW rfl _ (scOwSq_mono hGm hmono ζ)
        (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩)
  -- the second part: from `c = 1` to every code `c`
  have hC : ∀ R : SgT, SgWF S l R →
      (∀ K : SgC, SgWFC S l K → sgE K (leWe (sgV R) * 1) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → SgOwnC S b X0 K ∧ SgOwn S b X0 (fun r => sgE K (leWe r)) R) →
        ScDer S l Ow (sgE K (leWe (sgV R) * 1))
          (sgEh S l K (leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) 1))) →
      ∀ (K : SgC) (c : Ordinal.{0}), SgWFC S l K → GxCl (upsilon l) (ldAtR S l) c →
      1 ≤ c → c < Om (1 + 1) → sgE K (leWe (sgV R) * c) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → SgOwnC S b X0 K ∧ SgOwn S b X0 (fun r => sgE K (leWe r)) R ∧
        SgLimC S (fun z => sgE K (leWe (sgV R) * z)) c b X0) →
      ScDer S l Ow (sgE K (leWe (sgV R) * c)) (sgEh S l K (leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) c)) := by
    intro R hRw hB1 K c hKw hc hc1 hcW hv Ow hmono hown
    have hGm : Monotone (fun z => sgE K (leWe (sgV R) * z)) := fun _ _ h => sgE_mono K (leMulWe_mono h)
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨d, hd⟩ | hlim
    · subst h0; exact absurd hc1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hd
      subst hd
      have hdc := rqCode_pred hl hX hc hcW
      rcases eq_or_ne d 0 with rfl | hd0
      · rw [zero_add] at hv ⊢
        exact hB1 K hKw hv Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, (hown b X0 h).2.1⟩)
      · have hd1 : 1 ≤ d := Order.one_le_iff_ne_zero.2 hd0
        have e1 : sgV (SgT.term SgT.zero R d) + leWe (sgV R) * 1 = leWe (sgV R) * (d + 1) := by
          show 0 + leWe (sgV R) * d + leWe (sgV R) * 1 = _; rw [zero_add, mul_one, mul_add_one]
        have e2 : sgI S l (SgT.term SgT.zero R d) + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) 1 =
            leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) (d + 1) := by
          show 0 + leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) d +
            leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) 1 = _
          rw [zero_add, hΘ1, mul_one, rqTh_succ hl hX hdc, mul_add_one]
        have hD := hB1 (SgC.pfx K (SgT.term SgT.zero R d)) ⟨hKw, trivial, hRw, hdc, hd1, (lt_add_one d).trans hcW⟩
          (by show sgE K (sgV (SgT.term SgT.zero R d) + leWe (sgV R) * 1) = v; rw [e1]; exact hv) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hR, hcl⟩ := hown b X0 h
            have hle : ∀ y, sgE K y ≤ sgE K (0 + y) := fun y => sgE_mono K le_add_self
            refine ⟨⟨hK, trivial, sgOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => sgE_mono K (leWe_mono h))
              (fun _ _ h => sgE_mono K ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
              sgLimC_mono hGm (fun _ _ h => sgE_mono K ((add_le_add_iff_left _).2 (leMulWe_mono h)))
                (fun z => hle _) le_rfl le_rfl (sgLimC_le hcl le_self_add)⟩, ?_⟩
            exact sgOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => sgE_mono K (leWe_mono h))
              (fun _ _ h => sgE_mono K ((add_le_add_iff_left _).2 (leWe_mono h)))
              (fun y => sgE_mono K le_add_self) hR)
        exact sgDer_cast hD (by show sgE K (sgV (SgT.term SgT.zero R d) + leWe (sgV R) * 1) = _; rw [e1])
          (by show sgEh S l K (sgI S l (SgT.term SgT.zero R d) +
            leOe (sgI S l R) * gxTh (upsilon l) (ldAtR S l) 1) = _; rw [e2])
    · have hlimD := ScDer.lim (g := fun z => sgE K (leWe (sgV R) * z))
        (gh := fun v => sgEh S l K (leOe (sgI S l R) * v)) (Ow := Ow)
        (fun b X0 h => sgShp_path hl hX hKw hRw (hown b X0 h).1 (hown b X0 h).2.1) hmono hc hcW hlim
        (fun ζ hζ hζc => by
          have hζ1 := hlim.succ_lt hζc
          have hlt : sgE K (leWe (sgV R) * (ζ + 1)) < v := by rw [← hv]; exact sgE_strictMono K (leMulWe_lt hζ1)
          have hGm' : Monotone (fun z => leWe (sgE K (leWe (sgV R) * z))) := fun _ _ h => leWe_mono (hGm h)
          exact (IH _ hlt).2 K R (ζ + 1) hKw hRw (rqCode_succ hl hX hζ (hζ1.trans hcW)) le_add_self
            (hζ1.trans hcW) rfl _ (scOwSq_mono hGm' hmono (ζ + 1))
            (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2.1, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩))
      exact ScDer.weaken hlimD (fun b X0 h => ⟨h, (hown b X0 h).2.2 c le_rfl hlim⟩) hmono
  refine ⟨hA, fun K R => ?_⟩
  induction R generalizing K with
  | zero =>
    intro c hKw hRw
    refine hC SgT.zero hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw
    have e1 : leWe (sgV SgT.zero) * 1 = sgV SgT.zero + 1 := by
      show leWe 0 * 1 = 0 + 1; rw [leWe_zero, mul_one, zero_add]
    have e2 : leOe (sgI S l SgT.zero) * gxTh (upsilon l) (ldAtR S l) 1 = sgI S l SgT.zero + 1 := by
      show leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [leOe_zero, hΘ1, mul_one, zero_add]
    rw [e1, e2]
    exact hA K SgT.zero hKw trivial (by rw [← e1]; exact hv) Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, trivial⟩)
  | term P' R' c' _ IHR =>
    intro c hKw hRw
    obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
    refine hC (SgT.term P' R' c') ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ (fun K hKw hv Ow hmono hown => ?_) K c hKw
    have hD := IHR (SgC.pfx (SgC.lft K) P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W
      (by show sgE K (leWe (sgV P' + leWe (sgV R') * c')) = v; rw [← hv, mul_one]; rfl) Ow hmono
      (fun b X0 h => by
        obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
        exact ⟨⟨hK, hP⟩, hR, hcl⟩)
    exact sgDer_cast hD (by show sgE K (leWe (sgV P' + leWe (sgV R') * c')) = _; rw [mul_one]; rfl)
      (by show sgEh S l K (leOe (sgI S l P' + leOe (sgI S l R') * gxTh (upsilon l) (ldAtR S l) c')) = _
          rw [hΘ1, mul_one]; rfl)

omit hl hX in
/-- The own predicate of a term at the top level is monotone in the base and the offset. -/
theorem sgOwn_top_mono (t : SgT) : ∀ b β X0 X0', SgOwn S b X0 (fun y => y) t → b ≤ β → X0 ≤ X0' →
    SgOwn S β X0' (fun y => y) t :=
  fun _ _ _ _ h hb hX0 => sgOwn_mono hb hX0 t _ _ monotone_id monotone_id (fun _ => le_rfl) h

/-- **Every well-formed term `t` with `val t ≥ 1` is derived** (own predicate `SgOwn id t`, image `sgI t`). -/
theorem sgDer_term : ∀ t : SgT, SgWF S l t → 1 ≤ sgV t →
    ScDer S l (fun b X0 => SgOwn S b X0 (fun y => y) t) (sgV t) (sgI S l t)
  | .zero, _, h1 => absurd h1 (not_le.2 zero_lt_one)
  | .term P R c, ⟨hPw, hRw, hc, hc1, hcW⟩, _ =>
    (sgGen_all hl hX _).2 (SgC.pfx SgC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl _
      (sgOwn_top_mono _) (fun b X0 ⟨hP, hR, hcl⟩ => ⟨⟨trivial, hP⟩, hR, hcl⟩)

/-- **The level statement at every well-formed term**: `Sc.ScLev (SgOwn id t) (val t) (sgI t)`. -/
theorem sgLev_term (t : SgT) (ht : SgWF S l t) (h1 : 1 ≤ sgV t) :
    ScLev S l (fun b X0 => SgOwn S b X0 (fun y => y) t) (sgV t) (sgI S l t) :=
  (scDer_sound hl hX (sgDer_term hl hX t ht h1)).1

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Sg
