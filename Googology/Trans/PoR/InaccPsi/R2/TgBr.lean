import Googology.Trans.PoR.InaccPsi.R2.TgLevB

/-!
# The bridge with code levels: the closure condition gives the own predicate `TgOwn`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, codes = `Le.LeCl Ω₂ Q`.

* `tgEh` (the image evaluation of a context with the levels read by `Θ`), `TgWFC`, `TgOwnC` (own prefixes),
  `TgLevLe A K` (every level of the context `K` is `≤ A`), `TgDatC` (the data of the prefixes and of the levels
  above the bottom);
* `tgOwnC_dat` (**own prefixes and levels below the bottom give the data**), `tgShp_ctx` (**a shape with the fine
  laws carried through a context with code levels**: `Td.tdShp_vebC` at every node), `tgShp_path` (**the path shape
  `ζ ↦ K(W^F·ζ)` at the bottom `T_{K(W^F)}`** when the levels of `K` are below it);
* `tgBridge` (**THE BRIDGE WITH CODE LEVELS**: `TgOwnT` and `Tg.TgLevB` give `TgOwn` at a proper base, by
  `Sg.sgSq_supAt` on the path shapes), `tgOwn_of_cl` (**THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A
  PROPER BASE GIVES `TgOwn` OF ITS NORMAL-FORM TERM WITH CODE LEVELS**).

No new axiom.  New definitions: `tgEh`, `TgWFC`, `TgOwnC`, `TgLevLe`, `TgDatC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

/-- **The image evaluation of a context with the levels read by `Θ`.** -/
noncomputable def tgEh (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaC → Ordinal.{0} → Ordinal.{0}
  | .hole, v => v
  | .pfx K Q, v => tgEh S l K (tdIL S l Q + v)
  | .lft K, v => tgEh S l K (leOe v)
  | .phi K a, v => tgEh S l K (veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + v))

/-- Well-formed contexts with code levels. -/
def TgWFC (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TgWFC S l K ∧ TgWF S l Q
  | .lft K => TgWFC S l K
  | .phi K a => TgWFC S l K ∧ GxCl (upsilon l) (ldAtR S l) a ∧ 1 ≤ a ∧ a < Om (1 + 1)

/-- The own predicate of the prefixes of a context. -/
def TgOwnC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TgOwnC S b X0 K ∧ TgOwn S b X0 (taE K) Q
  | .lft K => TgOwnC S b X0 K
  | .phi K _ => TgOwnC S b X0 K

/-- Every level of the context is `≤ A`. -/
def TgLevLe (A : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K _ => TgLevLe A K
  | .lft K => TgLevLe A K
  | .phi K a => a ≤ A ∧ TgLevLe A K

/-- **The data of the prefixes and of the levels of a context** above the bottom `bot` (image bottom `Θ bot`). -/
def TgDatC (S : InaccSeq.{0}) (l bot : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TgDatC S l bot K ∧ taV Q ∈ cdHull S l ∧ taV Q ∈ S.CSet 0 bot ∧
      tdIL S l Q ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) bot) ∧
      (∀ Q', SC Q' → bot ≤ Q' → LeCl (Om (1 + 1)) Q' (taV Q)) ∧
      (∀ Q', SC Q' → gxTh (upsilon l) (ldAtR S l) bot ≤ Q' → LeCl (Om 1) Q' (tdIL S l Q))
  | .lft K => TgDatC S l bot K
  | .phi K a => TgDatC S l bot K ∧ GxCl (upsilon l) (ldAtR S l) a ∧ 1 ≤ a ∧ a < Om (1 + 1) ∧ a < bot

variable {S : InaccSeq.{0}}

theorem tgLevLe_mono {A A' : Ordinal.{0}} (h : A ≤ A') : ∀ K : TaC, TgLevLe A K → TgLevLe A' K
  | .hole, _ => trivial
  | .pfx K _, hK => tgLevLe_mono h K hK
  | .lft K, hK => tgLevLe_mono h K hK
  | .phi K _, ⟨ha, hK⟩ => ⟨ha.trans h, tgLevLe_mono h K hK⟩

section Ctx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Own prefixes and levels below the bottom give the data of a context.** -/
theorem tgOwnC_dat {b X0 A : Ordinal.{0}} : ∀ K : TaC, TgWFC S l K → TgOwnC S b X0 K → TgLevLe A K → ∀ y bot,
    S.psi (b + leWe (X0 + leWe (taE K y))) (Om (1 + 1)) ≤ bot → A < bot → TgDatC S l bot K
  | .hole, _, _, _, _, _, _, _ => trivial
  | .pfx K Q, ⟨hKw, hQw⟩, ⟨hKo, hQo⟩, hKl, y, bot, hbot, hA => by
    have hle : S.psi (b + leWe (X0 + leWe (taE K (taV Q)))) (Om (1 + 1)) ≤ bot :=
      ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (taE_mono K (le_self_add : taV Q ≤ taV Q + y)))))))).1.trans hbot
    obtain ⟨h1, h2, h3, h4⟩ := tgDat Q (taE K) (taE_mono K) hQw hQo
    exact ⟨tgOwnC_dat K hKw hKo hKl (taV Q + y) bot hbot hA, tgV_hull hl hX Q hQw, h1 bot hle,
      h2 _ (gxTh_mono hle), fun Q' hQ' h => h3 Q' hQ' (hle.trans h),
      fun Q' hQ' h => h4 Q' hQ' ((gxTh_mono hle).trans h)⟩
  | .lft K, hKw, hKo, hKl, y, bot, hbot, hA => tgOwnC_dat K hKw hKo hKl (leWe y) bot hbot hA
  | .phi K a, ⟨hKw, hac, ha1, haW⟩, hKo, ⟨haA, hKl⟩, y, bot, hbot, hA =>
    ⟨tgOwnC_dat K hKw hKo hKl (veblen a (Om (1 + 1) + y)) bot hbot hA, hac, ha1, haW, haA.trans_lt hA⟩

/-- **A shape with the fine laws carried through a context with code levels.** -/
theorem tgShp_ctx {bot : Ordinal.{0}} : ∀ K : TaC, TgDatC S l bot K →
    ∀ (g gh : Ordinal.{0} → Ordinal.{0}) (gs ghs : Ordinal.{0}),
    TaShp S l g gh gs ghs bot (gxTh (upsilon l) (ldAtR S l) bot) →
    TaShp S l (fun z => taE K (g z)) (fun v => tgEh S l K (gh v)) (taE K gs) (tgEh S l K ghs) bot
      (gxTh (upsilon l) (ldAtR S l) bot)
  | .hole, _, _, _, _, _, h => h
  | .pfx K Q, ⟨hK, hH, hm, hmh, hcl, hclh⟩, g, gh, gs, ghs, h =>
    tgShp_ctx K hK _ _ _ _ (taShp_pre hl hX h hH hm hmh hcl hclh)
  | .lft K, hK, g, gh, gs, ghs, h => tgShp_ctx K hK _ _ _ _ (taShp_lift hl hX h)
  | .phi K a, ⟨hK, hac, ha1, haW, hab⟩, g, gh, gs, ghs, h => by
    have hgs0 : 0 < gs := omega0_pos.trans_le h.shp.inf
    have hghs0 : 0 < ghs := omega0_pos.trans_le h.shp.infh
    have hpre := taShp_pre (E0 := Om (1 + 1)) (Eh0 := Om 1) hl hX h (mxOm2_mem _ _) (mxOm2_mem _ _)
      (CSet.Om_mem (CSet.one_mem _ _)) (fun _ _ _ => LeCl.om) (fun _ _ _ => LeCl.om)
    have hveb := tdShp_vebC hl hX hpre ha1 haW hac hab (lt_add_of_pos_right _ hgs0) (lt_add_of_pos_right _ hghs0)
    exact tgShp_ctx K hK _ _ _ _ hveb

/-- **The path shape `ζ ↦ K(W^F·ζ)`** at the bottom `T_{X₀ + W^{K(W^F·1)}}(b)`, when the levels of `K` are
`≤ A < bot`. -/
theorem tgShp_path {b X0 A : Ordinal.{0}} {K : TaC} {F : TaT} (hKw : TgWFC S l K) (hFw : TgWF S l F)
    (hKo : TgOwnC S b X0 K) (hFo : TgOwn S b X0 (fun r => taE K (leWe r)) F) (hKl : TgLevLe A K)
    (hA : A < leTe S (X0 + leWe (taE K (leWe (taV F) * 1))) b) :
    TaShp S l (fun z => taE K (leWe (taV F) * z)) (fun v => tgEh S l K (leOe (tdIL S l F) * v))
      (taE K (leWe (taV F + 1))) (tgEh S l K (leOe (tdIL S l F + 1)))
      (leTe S (X0 + leWe (taE K (leWe (taV F) * 1))) b)
      (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (taE K (leWe (taV F) * 1))) b)) := by
  set bot := leTe S (X0 + leWe (taE K (leWe (taV F) * 1))) b with hbot
  have hbot' : S.psi (b + leWe (X0 + leWe (taE K (leWe (taV F) * 1)))) (Om (1 + 1)) ≤ bot := le_rfl
  have hD := tgOwnC_dat hl hX K hKw hKo hKl _ bot hbot' hA
  have heF : Monotone (fun r => taE K (leWe r)) := fun _ _ h => taE_mono K (leWe_mono h)
  obtain ⟨h1, h2, h3, h4⟩ := tgDat (b := b) (X0 := X0) F _ heF hFw hFo
  have hle : S.psi (b + leWe (X0 + leWe ((fun r => taE K (leWe r)) (taV F)))) (Om (1 + 1)) ≤ bot := by
    rw [hbot]; unfold leTe; simp only [mul_one]; exact le_rfl
  have hlin := taShp_lin hl hX (F := taV F) (Fh := tdIL S l F) (bot := bot)
    (both := gxTh (upsilon l) (ldAtR S l) bot) (tgV_hull hl hX F hFw) (h1 bot hle) (h2 _ (gxTh_mono hle))
    (fun Q hQ h => h3 Q hQ (hle.trans h)) (fun Q hQ h => h4 Q hQ ((gxTh_mono hle).trans h))
  exact tgShp_ctx hl hX K hD _ _ _ _ hlin

end Ctx

section Bridge

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {β X0 Es : Ordinal.{0}}
  (hβd : leWe (X0 + leWe Es) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe Es) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe Es < S.psi 0 (Om (1 + 1 + 1)))

include hl hX hβd hβown hX0m hX0cl hX0G3

/-- **THE BRIDGE WITH CODE LEVELS**: the closure form `TgOwnT` and the bottoms `TgLevB` give `TgOwn` at a proper
base. -/
theorem tgBridge : ∀ (t : TaT) (K : TaC) (A : Ordinal.{0}), TgWFC S l K → TgWF S l t → TgOwnC S β X0 K →
    TgLevLe A K → TgOwnT S β X0 (taE K) t → TgLevB S β X0 A (taE K) t → taE K (taV t) ≤ Es →
    TgOwn S β X0 (taE K) t
  | .zero, _, _, _, _, _, _, _, _, _ => trivial
  | .phi a Y, K, A, hKw, ⟨hac, ha1, haW, hYw, _, _⟩, hKo, hKl, ⟨haT, hYT⟩, hYB, hEs =>
    ⟨haT, tgBridge Y (TaC.phi K a) (max A a) ⟨hKw, hac, ha1, haW⟩ hYw hKo
      ⟨le_max_right A a, tgLevLe_mono (le_max_left A a) K hKl⟩ hYT hYB hEs⟩
  | .term P R c, K, A, hKw, ⟨hPw, hRw, hc, hc1, hcW⟩, hKo, hKl, ⟨hPT, hRT, hcT⟩, ⟨hPB, hRB, hbotA⟩, hEs => by
    have hPle : taE K (taV P) ≤ Es := (taE_mono K (le_self_add : taV P ≤ taV P + leWe (taV R) * c)).trans hEs
    have hPo := tgBridge P K A hKw hPw hKo hKl hPT hPB hPle
    have hKPo : TgOwnC S β X0 (TaC.pfx K P) := ⟨hKo, hPo⟩
    have hRle : taE (TaC.lft (TaC.pfx K P)) (taV R) ≤ Es := by
      refine (taE_mono K ((add_le_add_iff_left _).2 ?_)).trans hEs
      simpa using leMulWe_mono (e := taV R) hc1
    have hRo := tgBridge R (TaC.lft (TaC.pfx K P)) A ⟨hKw, hPw⟩ hRw hKPo hKl hRT hRB hRle
    refine ⟨hPo, hRo, fun η hη hlim => ?_⟩
    have hA : A < leTe S (X0 + leWe (taE (TaC.pfx K P) (leWe (taV R) * 1))) β := by
      unfold leTe; simp only [mul_one]; exact hbotA
    have hsh := (tgShp_path hl hX (K := TaC.pfx K P) (F := R) ⟨hKw, hPw⟩ hRw hKPo hRo hKl hA).shp
    set g : Ordinal.{0} → Ordinal.{0} := fun z => taE (TaC.pfx K P) (leWe (taV R) * z) with hg
    have hGst : StrictMono (fun z => leWe (g z)) := fun _ _ h => leWe_lt (hsh.st h)
    have hgη : g η ≤ Es := (taE_mono (TaC.pfx K P) (leMulWe_mono hη)).trans hEs
    have hd1 : (1 : Ordinal.{0}) ≤ Om 1 := (gg_one_lt_of_SC Ph.ph_SC_Om1).le
    have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (hsh.st.monotone hd1)))))).1
    have hWle : leWe (X0 + leWe (g η)) ≤ leWe (X0 + leWe Es) :=
      leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hgη))
    exact sgSq_supAt (G := fun z => leWe (g z)) (Gs := leWe (taE (TaC.pfx K P) (leWe (taV R + 1)))) hGst
      (fun d hd => hβown d (hd.trans hWle)) hX0m
      (fun x c' hx hc' => leWe_mem (hsh.mem x c' hx (hbot.trans hc')))
      (fun x hx => leWe_mono (hsh.lt x hx).le)
      (fun Q hQ hc' => scShCl_lift hQ hsh.inf (hsh.cl Q hQ (hbot.trans hc')))
      ((leWe_dvd ((add_le_add_iff_left X0).2 (leWe_mono hgη))).trans hβd) hX0cl
      (lt_of_le_of_lt ((add_le_add_iff_left X0).2 (leWe_mono hgη)) hX0G3)
      (hcT η hη hlim)

end Bridge

section All

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES THE OWN PREDICATE `TgOwn` OF ITS
NORMAL-FORM TERM WITH CODE LEVELS** (every node level below `T` at its node, `Sg.SgLimC` at every coefficient). -/
theorem tgOwn_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < veblen (Om (1 + 1)) 1) : TgOwn S β X0 (fun y => y) (taTm E) := by
  obtain ⟨hw, -, hv⟩ := tgTm_spec hl hX E hEH hE
  have hT := tgOwnT_of_cl hl hX hβd hβown hX0cl hX0G3 hEcl hEH hE
  have hB := tgLevB_of_cl hl hX hβd hβown hX0cl hX0G3 hEcl hEH hE
  exact tgBridge hl hX (Es := E) hβd hβown hX0m hX0cl hX0G3 (taTm E) TaC.hole 0 trivial hw trivial trivial hT hB
    (by rw [hv]; exact le_rfl)

end All

end Googology.Trans.PoR.InaccPsi.R2.Tg
