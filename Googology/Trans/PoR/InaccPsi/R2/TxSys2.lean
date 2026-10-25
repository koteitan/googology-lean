import Googology.Trans.PoR.InaccPsi.R2.TxG

/-!
# The level system up to `W^{G+1} = G·Ω₂` (`G = φ(Ω₂, 1)`), its move under `B_n`, and the road

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`, `F_3 = ψ_{Ω₂}(W^{W^{G·Ω₂}})`.

`txGW S = G·Ω₂ = W^{G+1}` (the bound), `txTh2 S λ E` (the image: `Θ̂_L E` below `G`, `Ĝ·Θ c + Θ̂_L x` at
`E = G·c + x`, `x < G`).

* `txTh2_lt`, `txTh2_ge`, `txDecGW` (**every level `G ≤ E < G·Ω₂` of the hull is `G·c + x`**, `c` a code, `x < G`);
* `txLevGc` (the data of the level `G·c + x` over the prefix `G·c` of `Tx.txPDGc`);
* `txLS2` (**THE LEVEL SYSTEM UP TO `G·Ω₂`**), `txLSB2` (**ITS MOVE**: `B_n(G·c + x) = G·B_n c + B_n x`);
* `txAtMoveTop2` (**every atom `ψ_{Ω₂}(0) < s < F_3` moves** once the codes below it move), `TxAtMove23 S` (a
  hypothesis name: the move of the atoms `F_3 ≤ s ≤ θ`), `txAtMove22_of23`, `txAtMove23_of22`, `txAtMove17_of23`,
  `txRoad2` (**the road**), `txRoad2_hyps`.

No new axiom.  New definitions: `txGW`, `txTh2`, the hypothesis name `TxAtMove23`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

/-- **The bound `G·Ω₂ = W^{G+1}` of the level system.** -/
noncomputable def txGW (_S : InaccSeq.{0}) : Ordinal.{0} := veblen (Om (1 + 1)) 1 * Om (1 + 1)

/-- **The image of a level**: `Θ̂_L E` below `G`, `Ĝ·Θ(E / G) + Θ̂_L(E mod G)` above. -/
noncomputable def txTh2 (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if E < veblen (Om (1 + 1)) 1 then tdThL S l E
  else veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) (E / veblen (Om (1 + 1)) 1) +
    tdThL S l (E % veblen (Om (1 + 1)) 1)

theorem txTh2_lt {l E : Ordinal.{0}} (hE : E < veblen (Om (1 + 1)) 1) : txTh2 S l E = tdThL S l E := by
  unfold txTh2; rw [if_pos hE]

theorem txTh2_ge {l c x : Ordinal.{0}} (hc1 : 1 ≤ c) (hx : x < veblen (Om (1 + 1)) 1) :
    txTh2 S l (veblen (Om (1 + 1)) 1 * c + x) =
      veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) c + tdThL S l x := by
  have hG0 : veblen (Om (1 + 1 : Ordinal.{0})) 1 ≠ 0 := veblen_pos.ne'
  have hge : veblen (Om (1 + 1)) 1 ≤ veblen (Om (1 + 1)) 1 * c + x :=
    ((mul_one _).symm.le.trans (mul_le_mul_left' hc1 _)).trans le_self_add
  unfold txTh2
  rw [if_neg (not_lt.2 hge), Ordinal.mul_add_div _ hG0, Ordinal.div_eq_zero_of_lt hx, add_zero,
    Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx]

theorem txGW_lim : IsSuccLimit (txGW S) := isSuccLimit_mul_right veblen_pos ldOm2_SC.isSuccLimit

theorem txGW_lt_G3 : txGW S < S.psi 0 (Om (1 + 1 + 1)) := ldMul_lt_SC rwG3_SC tjG_lt_G3 rwW_lt_G3

/-- `G·2 ≤ G·Ω₂`. -/
theorem txGG_le_GW : txGG S ≤ txGW S := by
  have h : veblen (Om (1 + 1 : Ordinal.{0})) 1 + veblen (Om (1 + 1)) 1 = veblen (Om (1 + 1)) 1 * (1 + 1) := by
    rw [mul_add_one, mul_one]
  unfold txGG txGW
  rw [h]
  exact mul_le_mul_left' (ldOm2_SC.isSuccLimit.add_one_lt (gg_one_lt_of_SC ldOm2_SC)).le _

/-- `W^{G+1} = G·Ω₂`. -/
theorem txWG1 : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1 + 1) = veblen (Om (1 + 1)) 1 * Om (1 + 1) := by
  rw [leWe_succ, tgWe_G]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every level `G ≤ E < G·Ω₂` of the hull is `G·c + x`**: `c = E / G` a code, `1 ≤ c < Ω₂`, `x = E mod G` in
the hull. -/
theorem txDecGW {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < txGW S) :
    E = veblen (Om (1 + 1)) 1 * (E / veblen (Om (1 + 1)) 1) + E % veblen (Om (1 + 1)) 1 ∧
      GxCl (upsilon l) (ldAtR S l) (E / veblen (Om (1 + 1)) 1) ∧ 1 ≤ E / veblen (Om (1 + 1)) 1 ∧
      E / veblen (Om (1 + 1)) 1 < Om (1 + 1) ∧ E % veblen (Om (1 + 1)) 1 ∈ cdHull S l ∧
      E % veblen (Om (1 + 1)) 1 < veblen (Om (1 + 1)) 1 := by
  have hG0 : veblen (Om (1 + 1 : Ordinal.{0})) 1 ≠ 0 := veblen_pos.ne'
  have hWG : leWe (veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := tgWe_G
  have hcW : E / veblen (Om (1 + 1)) 1 < Om (1 + 1) := (Ordinal.div_lt hG0).2 hE
  have hEW : E < ω ^ (Om (1 + 1) * veblen (Om (1 + 1)) 1 + Om (1 + 1)) := by
    have : leWe (veblen (Om (1 + 1)) 1 + 1) = ω ^ (Om (1 + 1) * veblen (Om (1 + 1)) 1 + Om (1 + 1)) := by
      unfold leWe; rw [mul_add_one]
    rw [← this, txWG1]; exact hE
  have hcH : E / veblen (Om (1 + 1)) 1 ∈ cdHull S l := by
    have h := leDivOp_mem (K := Om (1 + 1) * veblen (Om (1 + 1)) 1) (dvd_mul_right _ _) hEH hEW
    have e0 : ω ^ (Om (1 + 1) * veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := hWG
    rwa [e0] at h
  have hxH : E % veblen (Om (1 + 1)) 1 ∈ cdHull S l := by
    have h := leModP_mem (Om (1 + 1) * veblen (Om (1 + 1)) 1) hEH
    have e0 : ω ^ (Om (1 + 1) * veblen (Om (1 + 1 : Ordinal.{0})) 1) = veblen (Om (1 + 1)) 1 := hWG
    rwa [e0] at h
  exact ⟨(Ordinal.div_add_mod E _).symm, (ldHull_iff hl hX hcW).1 hcH,
    Order.one_le_iff_pos.2 ((Ordinal.div_pos hG0).2 hGE), hcW, hxH, Ordinal.mod_lt _ hG0⟩

/-- **The data of the level `G·c + x`** (`c` a code, `1 ≤ c < Ω₂`, `x < G` in the hull). -/
theorem txLevGc {c x : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1))
    (hxH : x ∈ cdHull S l) (hxE : x < veblen (Om (1 + 1)) 1) :
    ScOwP S l (SnCL S (veblen (Om (1 + 1)) 1 * c + x)) (veblen (Om (1 + 1)) 1 * c + x)
        (veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) c + tdThL S l x) ∧
      ScLev S l (SnCL S (veblen (Om (1 + 1)) 1 * c + x)) (veblen (Om (1 + 1)) 1 * c + x)
        (veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) c + tdThL S l x) ∧
      veblen (Om 1) 1 * gxTh (upsilon l) (ldAtR S l) c + tdThL S l x < S.psi 0 (Om (1 + 1)) := by
  have hsH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
  have hsE : sgLW x < veblen (Om (1 + 1)) 1 := (txSg_le x).trans_lt hxE
  have hs2 : sgLW x + 1 < veblen (Om (1 + 1)) 1 := tjG_lim.add_one_lt hsE
  exact txLevXG hl hX x hxH hxE _ _ (txPDGc hl hX c hc hc1 hcW) ((tuWe_G hs2).2.trans (dvd_mul_right _ _))
    ((tuOe_Gh (txSucc_Gh hl hX hsH hsE)).2.trans (dvd_mul_right _ _))

/-- **THE LEVEL SYSTEM UP TO `W^{G+1} = G·Ω₂`.** -/
theorem txLS2 : StLS S l (txGW S) (txTh2 S) := by
  have hT := tjLS (S := S) hl hX
  refine ⟨txGW_lim, txGW_lt_G3, ?_, ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [txTh2_lt hlt]; exact hT.ltG E hEH h1 hlt
    · obtain ⟨hdec, hc, hc1, hcW, hxH, hxE⟩ := txDecGW hl hX hEH hge hE
      rw [hdec, txTh2_ge hc1 hxE]; exact (txLevGc hl hX hc hc1 hcW hxH hxE).2.2
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [txTh2_lt hlt]; exact hT.own E hEH h1 hlt
    · obtain ⟨hdec, hc, hc1, hcW, hxH, hxE⟩ := txDecGW hl hX hEH hge hE
      rw [hdec, txTh2_ge hc1 hxE]; exact (txLevGc hl hX hc hc1 hcW hxH hxE).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [txTh2_lt hlt]; exact hT.lev E hEH h1 hlt
    · obtain ⟨hdec, hc, hc1, hcW, hxH, hxE⟩ := txDecGW hl hX hEH hge hE
      rw [hdec, txTh2_ge hc1 hxE]; exact (txLevGc hl hX hc hc1 hcW hxH hxE).2.1

end Main

section Move

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **THE MOVE OF THE LEVEL SYSTEM UP TO `G·Ω₂`.** -/
theorem txLSB2 : StLSB S n l l' (txGW S) (txTh2 S) := by
  intro B hBSC hGB IHm E hEH h1 hE hEcl
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨hDε, hBε⟩ := tjB_G (S := S) (n := n)
  obtain ⟨hDεh, hBεh⟩ := tnB_Gh (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hGB_G : veblen (Om (1 + 1)) 1 ≤ txGW S :=
    (mul_one _).symm.le.trans (mul_le_mul_left' (gg_one_lt_of_SC ldOm2_SC).le _)
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
  · obtain ⟨hDE, hDE2, hBE2, hBEε, hBEH, hBcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
      tjB_thH hl hX hl' hX' hBSC IHm E hEH hlt hEcl
    refine ⟨hDE, hDE2, hBE2, hBEε.trans_le hGB_G, hBEH, hBcl, ?_, ?_, ?_, ?_⟩
    · rw [txTh2_lt hlt]; exact hDT
    · rw [txTh2_lt hlt]; exact hDΘ1
    · rw [txTh2_lt hlt]; exact hBΘ1
    · rw [txTh2_lt hlt, txTh2_lt hBEε]; exact hΘmove
  obtain ⟨hdec, hc, hc1, hcW, hxH, hxE⟩ := txDecGW hl hX hEH hge hE
  set G := veblen (Om (1 + 1 : Ordinal.{0})) 1 with hG_def
  set Gh := veblen (Om (1 : Ordinal.{0})) 1 with hGh_def
  set c := E / G with hc_def
  set x := E % G with hx_def
  rw [hdec] at hEcl ⊢
  have hWG : leWe G = G := tgWe_G
  have hcB' : LeCl (Om (1 + 1)) B c := by
    have h := swCl_divW hBSC (tnG_cl hBSC) hEcl
    rwa [hWG, Ordinal.mul_add_div _ veblen_pos.ne', Ordinal.div_eq_zero_of_lt hxE, add_zero] at h
  have hcB : c < B := LeCl.lt_of_lt hBSC hcB' hcW
  have hxB : LeCl (Om (1 + 1)) B x :=
    tuModW hBSC (by rw [hWG]; exact dvd_mul_right G c) (by rw [hWG]; exact hxE) hEcl
  obtain ⟨hDc, hBcc, hΘcc, hΘ'c⟩ := IHm c hc hcB
  obtain ⟨hDx, hDx2, hBx2, hBxG, hBxH, hBxcl, hDT, hDΘ1, hBΘ1, hΘmove⟩ :=
    tjB_thH hl hX hl' hX' hBSC IHm x hxH hxE hxB
  -- `B_n(G·c) = G·B_n c`
  set Pc : Ordinal.{0} → Prop := fun y => GxCl (upsilon l) (ldAtR S l) y ∧ y < B ∧ y < Om (1 + 1) with hPc
  have hPcD : ∀ y, Pc y → MvD S y := fun y hy => (IHm y hy.1 hy.2.1).1
  have hPcdec : ∀ y, Pc y → y ≠ 0 → Pc (log ω y) ∧ Pc (y - ω ^ log ω y) := fun y hy hy0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt y hy.1
    exact ⟨⟨hlog, (log_le_self ω y).trans_lt hy.2.1, (log_le_self ω y).trans_lt hy.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) (opow_log_le_self ω hy0), (Ordinal.sub_le_self _ _).trans_lt hy.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hy.2.2⟩⟩
  have hGopow : ω ^ G = G := gg_veblen_eps ldOm2_SC.1.ne'
  obtain ⟨hDGc, hBGc⟩ := leB_mulOp (n := n) hDε hBε Pc hPcD hPcdec
    (fun y hy => hy.2.2.trans tgOm_lt_G) c ⟨hc, hcB, hcW⟩
  rw [hGopow] at hDGc hBGc
  -- `B_n(Ĝ·Θ c) = Ĝ·B_n(Θ c)`
  have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
  set P1 : Ordinal.{0} → Prop := fun y => y < Om 1 ∧ y < Bc.bcC S (n + 1) with hP1
  have hP1D : ∀ y, P1 y → MvD S y := fun y hy => mvD_of_lt (hy.2.trans hLw)
  have hP1dec : ∀ y, P1 y → y ≠ 0 → P1 (log ω y) ∧ P1 (y - ω ^ log ω y) := fun y hy _ =>
    ⟨⟨(log_le_self ω y).trans_lt hy.1, (log_le_self ω y).trans_lt hy.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hy.1, (Ordinal.sub_le_self _ _).trans_lt hy.2⟩⟩
  have hGhopow : ω ^ Gh = Gh := gg_veblen_eps (Om_pos one_ne_zero).ne'
  have hΩGh : Om (1 : Ordinal.{0}) < Gh := (lt_add_one _).trans tnOm1_lt_Gh
  obtain ⟨hDGhc, hBGhc⟩ := leB_mulOp (n := n) hDεh hBεh P1 hP1D hP1dec (fun y hy => hy.1.trans hΩGh)
    (gxTh (upsilon l) (ldAtR S l) c) ⟨hΘcO, hΘcc⟩
  rw [hGhopow] at hDGhc hBGhc
  -- the parts after the move
  obtain ⟨hDE, hBE⟩ := mvB_add (k := n) hDGc hDx
  rw [hBGc] at hBE
  have hBcW : Bc.bcB S n c < Om (1 + 1) := by
    have := (mvB_lt_iff (k := n) hDc hD2).2 hcW; rwa [hB2] at this
  have hBc1 : 1 ≤ Bc.bcB S n c := by have := leB_le (n := n) hD1 hDc hc1; rwa [mwB_one] at this
  have e2 : Om (1 + 1) * (G * c + x) = G * c + Om (1 + 1) * x := by
    rw [mul_add, ← mul_assoc, tnK_mul_G]
  have e2' : Om (1 + 1) * (G * Bc.bcB S n c + Bc.bcB S n x) = G * Bc.bcB S n c + Om (1 + 1) * Bc.bcB S n x := by
    rw [mul_add, ← mul_assoc, tnK_mul_G]
  have e1h : ∀ z w : Ordinal.{0}, Om 1 * (Gh * z + w) = Gh * z + Om 1 * w := fun z w => by
    rw [mul_add, ← mul_assoc, tnK_mul_Gh]
  obtain ⟨hDE2, hBE2⟩ := mvB_add (k := n) hDGc hDx2
  rw [hBGc, hBx2] at hBE2
  obtain ⟨hDTh, hBTh⟩ := mvB_add (k := n) hDGhc hDT
  rw [hBGhc] at hBTh
  obtain ⟨hDTh2, hBTh2⟩ := mvB_add (k := n) hDGhc hDΘ1
  rw [hBGhc, hBΘ1] at hBTh2
  rw [txTh2_ge hc1 hxE]
  refine ⟨hDE, by rw [e2]; exact hDE2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2, hBE2, hBE, e2']
  · rw [hBE]
    calc G * Bc.bcB S n c + Bc.bcB S n x < G * Bc.bcB S n c + G := (add_lt_add_iff_left _).2 hBxG
      _ = G * (Bc.bcB S n c + 1) := (mul_add_one _ _).symm
      _ ≤ G * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hBcW) _
  · rw [hBE]
    have hBcH : Bc.bcB S n c ∈ cdHull S l' := (ldHull_iff hl' hX' hBcW).2 hBcc
    have h := leMulWe_mem (S := S) (tnG_mem (S := S)) hBcH
    rw [hWG] at h
    exact CSet.add_mem h hBxH
  · intro hDB Q hQ hQ'
    rw [hBE]
    have hBcQ : Bc.bcB S n c < Q := ((mvB_lt_iff (k := n) hDc hDB).2 hcB).trans_le hQ'
    have h := swCl_mulW hQ (tnG_cl hQ) (LeCl.small hBcQ)
    rw [hWG] at h
    exact LeCl.add h (hBxcl hDB Q hQ hQ')
  · exact hDTh
  · rw [e1h]; exact hDTh2
  · rw [e1h, hBTh2, hBTh, e1h]
  · rw [hBE, txTh2_ge hBc1 hBxG, hΘ'c, hΘmove, hBTh]

end Move

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{G·Ω₂}})` moves** once the codes below it move. -/
theorem txAtMoveTop2 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (txGW S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => txLS2 hl hX) (fun _ _ _ _ _ hl hX hl' hX' => txLSB2 hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `ψ_{Ω₂}(W^{W^{G·2}}) ≤ ψ_{Ω₂}(W^{W^{G·Ω₂}})`. -/
theorem txF2_le :
    S.psi (leWe (leWe (txGG S))) (Om (1 + 1)) ≤ S.psi (leWe (leWe (txGW S))) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leWe_mono txGG_le_GW))).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{G·Ω₂}}) ≤ s ≤ θ`.** -/
def TxAtMove23 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (txGW S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TxAtMove23` gives `TxAtMove22`.** -/
theorem txAtMove22_of23 (h : TxAtMove23 S) : TxAtMove22 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (txGW S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le
        (tnG_le_FN.trans (tuFN_le.trans (tuFU_le.trans (tuFE_le.trans (txF_le.trans hsT)))))
    exact txAtMoveTop2 hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`TxAtMove22` gives `TxAtMove23`.** -/
theorem txAtMove23_of22 (h : TxAtMove22 S) : TxAtMove23 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (txF2_le.trans hsT) hsθ IH

/-- **`TxAtMove23` gives `Tj.TjAtMove17`.** -/
theorem txAtMove17_of23 (h : TxAtMove23 S) : TjAtMove17 S := txAtMove17_of22 (txAtMove22_of23 h)

/-- **The road with `TxAtMove23`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem txRoad2 (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TxAtMove23 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  txRoad hU hO hL hV hN hlh (fun hν => txAtMove22_of23 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `txRoad2` follows from that of `Tx.txRoad`. -/
theorem txRoad2_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TxAtMove22 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TxAtMove23 S :=
  fun hν => txAtMove23_of22 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Tx
