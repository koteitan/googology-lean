import Googology.Trans.PoR.InaccPsi.R2.TaShp

/-!
# Shapes and data through contexts with Veblen nodes

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(b) = ψ_{Ω₂}(b + W^E)`, terms and contexts of
`Ta.TaT`, `Ta.TaC`.

* `TaDatC` (the data of the prefixes of a context above the bottoms, the small levels at the nodes), `taOwnC_dat`
  (**own prefixes have the data above `T_{X₀ + W^{K(y)}}(b)`**);
* `taShp_ctx` (**a shape with the fine laws carried through a context is a shape with the fine laws**: prefix,
  lift `W^·`, and at a node the prefix `Ω₂ + ·` followed by the lift through `φ(a, ·)`), `taShp_path` (**the path
  shape `ζ ↦ K(W^F·ζ)`** for every own term `F`);
* `taDatE` (**the data of `K(y)` from the data of `K` and of `y`**), `taOwP_succ` (**the own data `Sc.ScOwP` of
  `K(Q + 1)`** for every context `K` and every term `Q` own at `K`).

No new axiom.  New definition: `TaDatC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **The data of the prefixes of a context** above the bottoms. -/
def TaDatC (S : InaccSeq.{0}) (l bot both : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TaDatC S l bot both K ∧ taV Q ∈ cdHull S l ∧ taV Q ∈ S.CSet 0 bot ∧ taI S l Q ∈ S.CSet 0 both ∧
      (∀ Q', SC Q' → bot ≤ Q' → LeCl (Om (1 + 1)) Q' (taV Q)) ∧ (∀ Q', SC Q' → both ≤ Q' → LeCl (Om 1) Q' (taI S l Q))
  | .lft K => TaDatC S l bot both K
  | .phi K a => TaDatC S l bot both K ∧ TaSm a

section Ctx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Own prefixes have the data above `T_{X₀ + W^{K(y)}}(b)` for every `y`.** -/
theorem taOwnC_dat {b X0 : Ordinal.{0}} : ∀ K : TaC, TaWFC S l K → TaOwnC S b X0 K → ∀ y bot,
    S.psi (b + leWe (X0 + leWe (taE K y))) (Om (1 + 1)) ≤ bot →
    TaDatC S l bot (gxTh (upsilon l) (ldAtR S l) bot) K
  | .hole, _, _, _, _, _ => trivial
  | .pfx K Q, ⟨hKw, hQw⟩, ⟨hKo, hQo⟩, y, bot, hbot => by
    have hle : S.psi (b + leWe (X0 + leWe (taE K (taV Q)))) (Om (1 + 1)) ≤ bot :=
      ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (taE_mono K (le_self_add : taV Q ≤ taV Q + y)))))))).1.trans hbot
    obtain ⟨h1, h2, h3, h4⟩ := taDat hl hX Q (taE K) (taE_mono K) hQw hQo
    exact ⟨taOwnC_dat K hKw hKo (taV Q + y) bot hbot, taV_hull hl hX Q hQw, h1 bot hle,
      h2 _ (gxTh_mono hle), fun Q' hQ' h => h3 Q' hQ' (hle.trans h),
      fun Q' hQ' h => h4 Q' hQ' ((gxTh_mono hle).trans h)⟩
  | .lft K, hKw, hKo, y, bot, hbot => taOwnC_dat K hKw hKo (leWe y) bot hbot
  | .phi K a, ⟨hKw, ha⟩, hKo, y, bot, hbot =>
    ⟨taOwnC_dat K hKw hKo (veblen a (Om (1 + 1) + y)) bot hbot, ha⟩

/-- **A shape with the fine laws carried through a context is a shape with the fine laws.** -/
theorem taShp_ctx {bot both : Ordinal.{0}} (hbot : gamma 0 ≤ bot) (hboth : gamma 0 ≤ both) :
    ∀ K : TaC, TaDatC S l bot both K →
    ∀ (g gh : Ordinal.{0} → Ordinal.{0}) (gs ghs : Ordinal.{0}), TaShp S l g gh gs ghs bot both →
    TaShp S l (fun z => taE K (g z)) (fun v => taEh S l K (gh v)) (taE K gs) (taEh S l K ghs) bot both
  | .hole, _, _, _, _, _, h => h
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, g, gh, gs, ghs, h =>
    taShp_ctx hbot hboth K hK _ _ _ _ (taShp_pre hl hX h hH hm hmh hcl hclh)
  | .lft K, hK, g, gh, gs, ghs, h => taShp_ctx hbot hboth K hK _ _ _ _ (taShp_lift hl hX h)
  | .phi K a, ⟨hK, ha⟩, g, gh, gs, ghs, h => by
    have hgs0 : 0 < gs := omega0_pos.trans_le h.shp.inf
    have hghs0 : 0 < ghs := omega0_pos.trans_le h.shp.infh
    have hpre := taShp_pre (E0 := Om (1 + 1)) (Eh0 := Om 1) hl hX h (mxOm2_mem _ _) (mxOm2_mem _ _)
      (CSet.Om_mem (CSet.one_mem _ _)) (fun _ _ _ => LeCl.om) (fun _ _ _ => LeCl.om)
    have hveb := taShp_veb hl hX hpre ha hbot hboth (lt_add_of_pos_right _ hgs0) (lt_add_of_pos_right _ hghs0)
    exact taShp_ctx hbot hboth K hK _ _ _ _ hveb

/-- **The path shape `ζ ↦ K(W^F·ζ)`** at the bottom `T_{X₀ + W^{K(W^F·1)}}(b)`. -/
theorem taShp_path {b X0 : Ordinal.{0}} {K : TaC} {F : TaT} (hKw : TaWFC S l K) (hFw : TaWF S l F)
    (hKo : TaOwnC S b X0 K) (hFo : TaOwn S b X0 (fun r => taE K (leWe r)) F) :
    TaShp S l (fun z => taE K (leWe (taV F) * z)) (fun v => taEh S l K (leOe (taI S l F) * v))
      (taE K (leWe (taV F + 1))) (taEh S l K (leOe (taI S l F + 1)))
      (leTe S (X0 + leWe ((fun z => taE K (leWe (taV F) * z)) 1)) b)
      (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => taE K (leWe (taV F) * z)) 1)) b)) := by
  set bot := leTe S (X0 + leWe ((fun z => taE K (leWe (taV F) * z)) 1)) b with hbot
  have hbot' : S.psi (b + leWe (X0 + leWe (taE K (leWe (taV F) * 1)))) (Om (1 + 1)) ≤ bot := le_rfl
  have hD := taOwnC_dat hl hX K hKw hKo _ bot hbot'
  have heF : Monotone (fun r => taE K (leWe r)) := fun _ _ h => taE_mono K (leWe_mono h)
  obtain ⟨h1, h2, h3, h4⟩ := taDat hl hX (b := b) (X0 := X0) F _ heF hFw hFo
  have hle : S.psi (b + leWe (X0 + leWe ((fun r => taE K (leWe r)) (taV F)))) (Om (1 + 1)) ≤ bot := by
    rw [hbot]; unfold leTe; simp only [mul_one]; exact le_rfl
  have hgb : gamma 0 ≤ bot := taGam_le_psi2 _
  have hlin := taShp_lin hl hX (F := taV F) (Fh := taI S l F) (bot := bot)
    (both := gxTh (upsilon l) (ldAtR S l) bot) (taV_hull hl hX F hFw) (h1 bot hle) (h2 _ (gxTh_mono hle))
    (fun Q hQ h => h3 Q hQ (hle.trans h)) (fun Q hQ h => h4 Q hQ ((gxTh_mono hle).trans h))
  exact taShp_ctx hl hX hgb (taTh_gam hl hX hgb) K hD _ _ _ _ hlin

/-- **The data of `K(y)`** from the data of the prefixes of `K` and of `y`. -/
theorem taDatE {bot both : Ordinal.{0}} (hbot : gamma 0 ≤ bot) (hboth : gamma 0 ≤ both) :
    ∀ K : TaC, TaDatC S l bot both K → ∀ y yh,
    y ∈ cdHull S l → y ∈ S.CSet 0 bot → yh ∈ S.CSet 0 both →
    (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q y) → (∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q yh) →
    taE K y ∈ cdHull S l ∧ taE K y ∈ S.CSet 0 bot ∧ taEh S l K yh ∈ S.CSet 0 both ∧
      (∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q (taE K y)) ∧ (∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q (taEh S l K yh))
  | .hole, _, _, _, h1, h2, h3, h4, h5 => ⟨h1, h2, h3, h4, h5⟩
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, y, yh, h1, h2, h3, h4, h5 =>
    taDatE hbot hboth K hK _ _ (CSet.add_mem hH h1) (CSet.add_mem hm h2)
      (CSet.add_mem hmh h3) (fun Q' hQ' hb => LeCl.add (hcl Q' hQ' hb) (h4 Q' hQ' hb))
      (fun Q' hQ' hb => LeCl.add (hclh Q' hQ' hb) (h5 Q' hQ' hb))
  | .lft K, hK, y, yh, h1, h2, h3, h4, h5 =>
    taDatE hbot hboth K hK _ _ (leWe_mem h1) (leWe_mem h2) (leOe_mem h3)
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' ldOm2_SC _ (h4 Q' hQ' hb)))
      (fun Q' hQ' hb => LeCl.opow hQ'.1 (LeCl.mulK hQ' Ph.ph_SC_Om1 _ (h5 Q' hQ' hb)))
  | .phi K a, ⟨hK, ha⟩, y, yh, h1, h2, h3, h4, h5 =>
    taDatE hbot hboth K hK _ _
      (CSet.phi_mem (taSm_hull hl hX ha) (CSet.add_mem (mxOm2_mem _ _) h1))
      (CSet.phi_mem (taSm_mem ha hbot) (CSet.add_mem (mxOm2_mem _ _) h2))
      (CSet.phi_mem (taSm_mem ha hboth) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) h3))
      (fun Q' hQ' hb => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ')) (LeCl.add LeCl.om (h4 Q' hQ' hb)))
      (fun Q' hQ' hb => LeCl.phi (LeCl.small (taSm_lt_SC ha hQ')) (LeCl.add LeCl.om (h5 Q' hQ' hb)))

/-- **The own data of `K(Q + 1)`** for every context `K` and term `Q` own at `K`. -/
theorem taOwP_succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {K : TaC} {Q : TaT} (hKw : TaWFC S l K)
    (hQw : TaWF S l Q) (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')
    (hown : ∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (taE K) Q) :
    ScOwP S l Ow (taE K (taV Q + 1)) (taEh S l K (taI S l Q + 1)) := by
  refine ⟨fun b X0 hOw => ?_, hmono⟩
  obtain ⟨hKo, hQo⟩ := hown b X0 hOw
  set T := S.psi (b + leWe (X0 + leWe (taE K (taV Q + 1)))) (Om (1 + 1)) with hT
  have hgT : gamma 0 ≤ T := taGam_le_psi2 _
  have hD := taOwnC_dat hl hX K hKw hKo (taV Q + 1) T le_rfl
  obtain ⟨h1, h2, h3, h4⟩ := taDat hl hX Q (taE K) (taE_mono K) hQw hQo
  have hle : S.psi (b + leWe (X0 + leWe (taE K (taV Q)))) (Om (1 + 1)) ≤ T :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
      ((add_le_add_iff_left X0).2 (leWe_mono (taE_mono K (le_self_add : taV Q ≤ taV Q + 1))))))).1
  obtain ⟨a1, a2, a3, a4, a5⟩ := taDatE hl hX hgT (taTh_gam hl hX hgT) K hD (taV Q + 1) (taI S l Q + 1)
    (CSet.succ_mem (taV_hull hl hX Q hQw)) (CSet.succ_mem (h1 T hle)) (CSet.succ_mem (h2 _ (gxTh_mono hle)))
    (fun Q' hQ' hb => LeCl.add (h3 Q' hQ' (hle.trans hb)) (LeCl.small (gg_one_lt_of_SC hQ')))
    (fun Q' hQ' hb => LeCl.add (h4 Q' hQ' ((gxTh_mono hle).trans hb)) (LeCl.small (gg_one_lt_of_SC hQ')))
  have h1E : (1 : Ordinal.{0}) ≤ taE K (taV Q + 1) := le_add_self.trans (taE_strictMono K).le_apply
  exact ⟨h1E, a1, a2, a3, a4, a5⟩

end Ctx

end Googology.Trans.PoR.InaccPsi.R2.Ta
