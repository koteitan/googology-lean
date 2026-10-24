import Googology.Trans.PoR.InaccPsi.R2.TgBr

/-!
# The strong level condition and the own predicate of the node derivation with code levels

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `T_y(b, X₀) = ψ_{Ω₂}(b + W^{X₀ + W^y})`, `φ = veblen`.

* `TjSLC b X₀ e a` (**THE STRONG LEVEL CONDITION** of a node at level `a` evaluated by the outer map `e`: every
  `η ≤ a` is below `T_{e(φ(η, Ω₂ + 1))}`; it is kept by the members of a node, whose levels are `≤ a`, and it
  holds at every node of a normal form by the code gap, `Tj.tjOwn_of_cl`);
* `TjOwn` (the strong level condition at every node, `Sg.SgLimC` at every coefficient), `TjOwnC` (own prefixes and
  the strong level condition at every level of a context);
* `tjSLC_mono`, `tjSLC_le`, `tjOwn_mono`, `tjOwnC_mono`, `tjOwn_tg`, `tjOwnC_tg` (**`TjOwn` gives `Tg.TgOwn`**),
  `tjOwn_cat`;
* `tjOwnC_lev` (**every level of an own context is below `T_{K(h)}` for every hole value `h ≥ 1`**), `tgEh_normal`,
  `tjDatE` (the data of `K(y)`), `tjE_lt_G3`, `tjOwP_succ` (**the own data of `K(Q + 1)`**).

No new axiom.  New definitions: `TjSLC`, `TjOwn`, `TjOwnC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

/-- **The strong level condition** of a node at level `a` with the outer evaluation `e`. -/
def TjSLC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) (e : Ordinal.{0} → Ordinal.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ η, η ≤ a → η < S.psi (b + leWe (X0 + leWe (e (veblen η (Om (1 + 1) + 1))))) (Om (1 + 1))

/-- **The own predicate of the node derivation**: the strong level condition at every node, `Sg.SgLimC` at every
coefficient. -/
def TjOwn (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => TjSLC S b X0 e a ∧ TjOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R c => TjOwn S b X0 e P ∧ TjOwn S b X0 (fun r => e (taV P + leWe r)) R ∧
      SgLimC S (fun z => e (taV P + leWe (taV R) * z)) c b X0

/-- The own predicate of a context: own prefixes, the strong level condition at every level. -/
def TjOwnC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TjOwnC S b X0 K ∧ TjOwn S b X0 (taE K) Q
  | .lft K => TjOwnC S b X0 K
  | .phi K a => TjOwnC S b X0 K ∧ TjSLC S b X0 (taE K) a

variable {S : InaccSeq.{0}}

theorem tjT_mono {b b' X0 X0' x y : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') (h : x ≤ y) :
    S.psi (b + leWe (X0 + leWe x)) (Om (1 + 1)) ≤ S.psi (b' + leWe (X0' + leWe y)) (Om (1 + 1)) :=
  scTop_mono hb hX h

theorem tjSLC_mono {b b' X0 X0' a : Ordinal.{0}} {e e' : Ordinal.{0} → Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0')
    (hle : ∀ y, e y ≤ e' y) (h : TjSLC S b X0 e a) : TjSLC S b' X0' e' a :=
  fun η hη => (h η hη).trans_le (tjT_mono hb hX (hle _))

theorem tjSLC_le {b X0 a a' : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (ha : a' ≤ a) (h : TjSLC S b X0 e a) :
    TjSLC S b X0 e a' := fun η hη => h η (hη.trans ha)

theorem tjOwn_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ (t : TaT) (e e' : Ordinal.{0} → Ordinal.{0}), Monotone e → Monotone e' → (∀ y, e y ≤ e' y) →
      TjOwn S b X0 e t → TjOwn S b' X0' e' t
  | .zero, _, _, _, _, _, _ => trivial
  | .phi a Y, e, e', he, he', hle, ⟨hs, h⟩ =>
    ⟨tjSLC_mono hb hX hle hs, tjOwn_mono hb hX Y _ _ (fun _ _ h => he (taNode_mono _ a h))
      (fun _ _ h => he' (taNode_mono _ a h)) (fun y => hle _) h⟩
  | .term P R c, e, e', he, he', hle, ⟨hP, hR, hc⟩ => by
    refine ⟨tjOwn_mono hb hX P e e' he he' hle hP,
      tjOwn_mono hb hX R _ _ (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
      sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => hle _) hb hX hc⟩

theorem tjOwnC_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ K : TaC, TjOwnC S b X0 K → TjOwnC S b' X0' K
  | .hole, _ => trivial
  | .pfx K Q, ⟨hK, hQ⟩ => ⟨tjOwnC_mono hb hX K hK,
      tjOwn_mono hb hX Q _ _ (taE_mono K) (taE_mono K) (fun _ => le_rfl) hQ⟩
  | .lft K, hK => tjOwnC_mono hb hX K hK
  | .phi K _, ⟨hK, hs⟩ => ⟨tjOwnC_mono hb hX K hK, tjSLC_mono hb hX (fun _ => le_rfl) hs⟩

theorem tjOwn_top_mono (t : TaT) : ∀ b β X0 X0', TjOwn S b X0 (fun y => y) t → b ≤ β → X0 ≤ X0' →
    TjOwn S β X0' (fun y => y) t :=
  fun _ _ _ _ h hb hX0 => tjOwn_mono hb hX0 t _ _ monotone_id monotone_id (fun _ => le_rfl) h

/-- **`TjOwn` gives `Tg.TgOwn`** (the level condition at a node is the case `η = a`). -/
theorem tjOwn_tg {l b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TgWF S l t → TjOwn S b X0 e t → TgOwn S b X0 e t
  | .zero, _, _, _, _ => trivial
  | .phi a Y, e, he, ⟨_, _, _, hYw, hY1, _⟩, ⟨hs, hY⟩ =>
    ⟨(hs a le_rfl).trans_le (tjT_mono le_rfl le_rfl (he (taNode_mono _ a hY1))),
      tjOwn_tg Y _ (fun _ _ h => he (taNode_mono _ a h)) hYw hY⟩
  | .term P R _, e, he, ⟨hPw, hRw, _⟩, ⟨hP, hR, hc⟩ =>
    ⟨tjOwn_tg P e he hPw hP, tjOwn_tg R _ (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))) hRw hR, hc⟩

theorem tjOwnC_tg {l b X0 : Ordinal.{0}} : ∀ K : TaC, TgWFC S l K → TjOwnC S b X0 K → TgOwnC S b X0 K
  | .hole, _, _ => trivial
  | .pfx K Q, ⟨hKw, hQw⟩, ⟨hK, hQ⟩ => ⟨tjOwnC_tg K hKw hK, tjOwn_tg Q _ (taE_mono K) hQw hQ⟩
  | .lft K, hKw, hK => tjOwnC_tg K hKw hK
  | .phi K _, ⟨hKw, _⟩, ⟨hK, _⟩ => tjOwnC_tg K hKw hK

/-- **The own predicate of a concatenation.** -/
theorem tjOwn_cat {l b X0 : Ordinal.{0}} {A : TaT} : ∀ (B : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TgWF S l B → TjOwn S b X0 e A → TjOwn S b X0 (fun y => e (taV A + y)) B → TjOwn S b X0 e (taCat A B)
  | .zero, _, _, _, hA, _ => hA
  | .phi a Y, e, he, _, hA, hB => by
    refine ⟨hA, ?_, sgLimC_one⟩
    show TjOwn S b X0 (fun y => e (taV A + leWe y)) (TaT.phi a Y)
    exact tjOwn_mono le_rfl le_rfl (TaT.phi a Y) _ _ (fun _ _ h => he ((add_le_add_iff_left _).2 h))
      (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h)))
      (fun y => he ((add_le_add_iff_left _).2 (taLe_We _))) hB
  | .term P R c, e, he, ⟨hPw, _⟩, hA, ⟨hP, hR, hc⟩ => by
    have eV := tgV_cat A P hPw
    refine ⟨tjOwn_cat P e he hPw hA hP, ?_, ?_⟩
    · refine tjOwn_mono le_rfl le_rfl R _ _
        (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => ?_) hR
      show e (taV A + (taV P + leWe y)) ≤ e (taV (taCat A P) + leWe y)
      rw [eV, add_assoc]
    · refine sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leMulWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => ?_) le_rfl le_rfl hc
      show e (taV A + (taV P + leWe (taV R) * z)) ≤ e (taV (taCat A P) + leWe (taV R) * z)
      rw [eV, add_assoc]

/-- **Every level of an own context is below `T_{K(h)}` for every hole value `h ≥ 1`.** -/
theorem tjOwnC_lev {b X0 : Ordinal.{0}} : ∀ K : TaC, TjOwnC S b X0 K → ∀ h, 1 ≤ h →
    ∃ A, TgLevLe A K ∧ A < S.psi (b + leWe (X0 + leWe (taE K h))) (Om (1 + 1))
  | .hole, _, _, _ => ⟨0, trivial, (SC_psi (InR_Om_succ 1) _).1⟩
  | .pfx K Q, ⟨hK, _⟩, h, h1 => tjOwnC_lev K hK (taV Q + h) (h1.trans le_add_self)
  | .lft K, hK, h, _ => tjOwnC_lev K hK (leWe h) (Order.one_le_iff_pos.2 (leWe_pos h))
  | .phi K a, ⟨hK, hs⟩, h, h1 => by
    obtain ⟨A, hA, hlt⟩ := tjOwnC_lev K hK (veblen a (Om (1 + 1) + h)) (Order.one_le_iff_pos.2 veblen_pos)
    refine ⟨max A a, ⟨le_max_right A a, tgLevLe_mono (le_max_left A a) K hA⟩, max_lt hlt ?_⟩
    exact (hs a le_rfl).trans_le (tjT_mono le_rfl le_rfl (taE_mono K (taNode_mono _ a h1)))

theorem tgEh_normal (l : Ordinal.{0}) : ∀ K : TaC, Order.IsNormal (tgEh S l K)
  | .hole => Order.IsNormal.id
  | .pfx K Q => (tgEh_normal l K).comp (isNormal_add_right (tdIL S l Q))
  | .lft K => (tgEh_normal l K).comp ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right (Om_pos one_ne_zero)))
  | .phi K a => (tgEh_normal l K).comp (taNode_normal _ _)

theorem tgEh_strictMono (l : Ordinal.{0}) (K : TaC) : StrictMono (tgEh S l K) := (tgEh_normal l K).strictMono

theorem tgEh_mono (l : Ordinal.{0}) (K : TaC) : Monotone (tgEh S l K) := (tgEh_strictMono l K).monotone

section Ctx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The data of `K(y)`** from the data of the prefixes and the levels of `K` and of `y`. -/
theorem tjDatE {bot : Ordinal.{0}} : ∀ K : TaC, TgDatC S l bot K → ∀ y yh,
    y ∈ cdHull S l → y ∈ S.CSet 0 bot → yh ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) bot) →
    (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q y) →
    (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) bot ≤ Q → LeCl (Om 1) Q yh) →
    taE K y ∈ cdHull S l ∧ taE K y ∈ S.CSet 0 bot ∧
      tgEh S l K yh ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) bot) ∧
      (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q (taE K y)) ∧
      (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) bot ≤ Q → LeCl (Om 1) Q (tgEh S l K yh))
  | .hole, _, _, _, h1, h2, h3, h4, h5 => ⟨h1, h2, h3, h4, h5⟩
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, y, yh, h1, h2, h3, h4, h5 =>
    tjDatE K hK _ _ (CSet.add_mem hH h1) (CSet.add_mem hm h2)
      (CSet.add_mem hmh h3) (fun Q' hQ' hb => LeCl.add (hcl Q' hQ' hb) (h4 Q' hQ' hb))
      (fun Q' hQ' hb => LeCl.add (hclh Q' hQ' hb) (h5 Q' hQ' hb))
  | .lft K, hK, y, yh, h1, h2, h3, h4, h5 =>
    tjDatE K hK _ _ (leWe_mem h1) (leWe_mem h2) (leOe_mem h3)
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' ldOm2_SC _ (h4 Q' hQ' hb)))
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' Ph.ph_SC_Om1 _ (h5 Q' hQ' hb)))
  | .phi K a, ⟨hK, hac, _, haW, hab⟩, y, yh, h1, h2, h3, h4, h5 => by
    have hΘa : gxTh (upsilon l) (ldAtR S l) a < gxTh (upsilon l) (ldAtR S l) bot := gxTh_lt hac hab
    exact tjDatE K hK _ _
      (CSet.phi_mem ((ldHull_iff hl hX haW).2 hac) (CSet.add_mem (mxOm2_mem _ _) h1))
      (CSet.phi_mem (CSet.of_lt hab) (CSet.add_mem (mxOm2_mem _ _) h2))
      (CSet.phi_mem (CSet.of_lt hΘa) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) h3))
      (fun Q' _ hb => LeCl.phi (LeCl.small (hab.trans_le hb)) (LeCl.add LeCl.om (h4 Q' ‹_› hb)))
      (fun Q' _ hb => LeCl.phi (LeCl.small (hΘa.trans_le hb)) (LeCl.add LeCl.om (h5 Q' ‹_› hb)))

/-- Contexts stay below `ψ_{Ω₃}(0)` and their images below `ψ_{Ω₂}(0)`. -/
theorem tjE_lt_G3 : ∀ K : TaC, TgWFC S l K → ∀ y yh, y < S.psi 0 (Om (1 + 1 + 1)) → yh < S.psi 0 (Om (1 + 1)) →
    taE K y < S.psi 0 (Om (1 + 1 + 1)) ∧ tgEh S l K yh < S.psi 0 (Om (1 + 1))
  | .hole, _, _, _, h1, h2 => ⟨h1, h2⟩
  | .pfx K Q, ⟨hK, hQ⟩, y, yh, h1, h2 => by
    obtain ⟨a1, a2⟩ := tgV_lt_G3 hl hX Q hQ
    exact tjE_lt_G3 K hK _ _ (rwG3_SC.isPrincipal a1 h1) (rwG_SC.isPrincipal a2 h2)
  | .lft K, hK, y, yh, h1, h2 =>
    tjE_lt_G3 K hK _ _ (leWe_lt_SC rwG3_SC rwW_lt_G3 h1).1 (leOe_lt_SC rwG_SC rwO_lt_G h2).1
  | .phi K a, ⟨hK, _, _, haW⟩, y, yh, h1, h2 => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    exact tjE_lt_G3 K hK _ _ (hG3.2 a (haW.trans rwW_lt_G3) _ (hG3.isPrincipal rwW_lt_G3 h1))
      (hG1.2 _ ((Sn.snTh_lt_Om1 hl hX haW.le).trans rwO_lt_G) _ (hG1.isPrincipal rwO_lt_G h2))

/-- **The own data of `K(Q + 1)`** for every context `K` and term `Q` with `TjOwnC K` and `TjOwn (K ·) Q`. -/
theorem tjOwP_succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {K : TaC} {Q : TaT} (hKw : TgWFC S l K)
    (hQw : TgWF S l Q) (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')
    (hown : ∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (taE K) Q) :
    ScOwP S l Ow (taE K (taV Q + 1)) (tgEh S l K (tdIL S l Q + 1)) := by
  refine ⟨fun b X0 hOw => ?_, hmono⟩
  obtain ⟨hKo, hQo⟩ := hown b X0 hOw
  set T := S.psi (b + leWe (X0 + leWe (taE K (taV Q + 1)))) (Om (1 + 1)) with hT
  obtain ⟨A, hAK, hAT⟩ := tjOwnC_lev K hKo (taV Q + 1) le_add_self
  have hD := tgOwnC_dat hl hX K hKw (tjOwnC_tg K hKw hKo) hAK (taV Q + 1) T le_rfl hAT
  obtain ⟨h1, h2, h3, h4⟩ := tgDat Q (taE K) (taE_mono K) hQw (tjOwn_tg Q _ (taE_mono K) hQw hQo)
  have hle : S.psi (b + leWe (X0 + leWe (taE K (taV Q)))) (Om (1 + 1)) ≤ T :=
    tjT_mono le_rfl le_rfl (taE_mono K (le_self_add : taV Q ≤ taV Q + 1))
  obtain ⟨a1, a2, a3, a4, a5⟩ := tjDatE hl hX K hD (taV Q + 1) (tdIL S l Q + 1)
    (CSet.succ_mem (tgV_hull hl hX Q hQw)) (CSet.succ_mem (h1 T hle)) (CSet.succ_mem (h2 _ (gxTh_mono hle)))
    (fun Q' hQ' hb => LeCl.add (h3 Q' hQ' (hle.trans hb)) (LeCl.small (gg_one_lt_of_SC hQ')))
    (fun Q' hQ' hb => LeCl.add (h4 Q' hQ' ((gxTh_mono hle).trans hb)) (LeCl.small (gg_one_lt_of_SC hQ')))
  have h1E : (1 : Ordinal.{0}) ≤ taE K (taV Q + 1) := le_add_self.trans (taE_strictMono K).le_apply
  exact ⟨h1E, a1, a2, a3, a4, a5⟩

end Ctx

end Googology.Trans.PoR.InaccPsi.R2.Tj
