import Googology.Trans.PoR.InaccPsi.R2.ScOm

/-!
# Exponent shapes and the level step `members ⇒ top`: one statement for every level

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`.

An **exponent shape** (`ScShp S λ g ĝ g* ĝ* bot bôt`): the exponents `g ζ` (code parameters `ζ < Ω₂`, strictly
monotone, below the limit exponent `g* ≥ ω`) with the images `ĝ v` (`v < Ω₁`, below `ĝ* ≥ ω`); `g ζ` in the hull,
`g*` in the hull; `g`, `ĝ` keep the closures above the bottoms `bot`, `bôt`; the closure laws `ScShCl g g* Q`
(generator `Ω₂`) and `ScImCl ĝ ĝ* Q` (generator `Ω₁`) at every strongly critical `Q` above the bottom; and the
index (every hull `c < g*` is below `g(q+1)` for a code `q` with `g q ≤ c` if `q ≠ 0`); the members and `g*`
(and their images) codes `LeCl` over every such `Q`, `g*`, `ĝ*` in the closures above the bottoms; `ĝ` strictly
monotone and continuous at limits.  The bottoms at the base
`b` and the offset `X₀` are `T_{X₀ + W^{g 1}}(b)` and its reading: the shape asks its constants to be own there.

**The level step** (`scLev_om`): if a shape is valid under the own predicate `Ow` (at every `b`, `X₀` with
`Ow b X₀`), `Ow` is monotone, and every member `g ζ` (`ζ ≥ 1` a code) has the level statement with the image
`ĝ(Θ ζ)` and the own predicate `Ow b X₀ ∧ ∃ j, ζ < SQ_j(X₀, b)` (`SQ` of the lifted shape `ζ ↦ W^{g ζ}`), then the
limit exponent `g*` has the level statement with the image `ĝ*`:
`Θ(T_{X₀ + W^{g*}}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{ĝ*}})`.  This is the same theorem at every level: the members may
be codes (`Sc.scShp_code`, giving the top at `W^{Ω₂}` over every offset), exponents `≥ Ω₂`, or exponents of any
later level.

* `ScImCl`, `scShCl_lift`, `scImCl_lift`, `scIdx_lift` (the closure laws and the index pass from `g` to `W^g`);
* `scShCl_code`, `scImCl_code`, `scShp_code` (the base shape `g ζ = ζ`, `g* = Ω₂`, `ĝ v = v`, `ĝ* = Ω₁`);
* `scLev_om` (**THE LEVEL STEP**), `scSq_code` (`SQ` of `ζ ↦ W^ζ` is `Rw.rwEX`), `scLev_W` (**the top at
  `W^{Ω₂}` over every offset `X₀` and base bound `b`: `ScLev ⊤ Ω₂ Ω₁`**).

No new axiom.  New definitions: `ScImCl`, `ScShp`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

/-- **The closure law of an image shape `ĝ` with top `ĝ*` at `Q`** (generator `Ω₁`). -/
def ScImCl (Gh : Ordinal.{0} → Ordinal.{0}) (Ghs Q : Ordinal.{0}) : Prop :=
  ∀ w, LeCl (Om 1) Q w → w < Om 1 * Ghs → ∃ v, v < Q ∧ w < Om 1 * Gh (v + 1)

/-- **An exponent shape** with its image shape, above the bottoms `bot`, `bôt`. -/
structure ScShp (S : InaccSeq.{0}) (l : Ordinal.{0}) (g gh : Ordinal.{0} → Ordinal.{0})
    (gs ghs bot both : Ordinal.{0}) : Prop where
  st : StrictMono g
  lt : ∀ ζ, ζ < Om (1 + 1) → g ζ < gs
  lth : ∀ v, v < Om 1 → gh v < ghs
  inf : ω ≤ gs
  infh : ω ≤ ghs
  hull : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < Om (1 + 1) → g ζ ∈ cdHull S l
  hullS : gs ∈ cdHull S l
  mem : ∀ x c, x ∈ S.CSet 0 c → bot ≤ c → g x ∈ S.CSet 0 c
  memh : ∀ v c, v ∈ S.CSet 0 c → both ≤ c → gh v ∈ S.CSet 0 c
  cl : ∀ Q, SC Q → bot ≤ Q → ScShCl g gs Q
  clh : ∀ Q, SC Q → both ≤ Q → ScImCl gh ghs Q
  idx : ∀ c, c ∈ cdHull S l → c < gs → ∃ q, GxCl (upsilon l) (ldAtR S l) q ∧ q < Om (1 + 1) ∧
    c < g (q + 1) ∧ (q ≠ 0 → g q ≤ c)
  clm : ∀ Q, SC Q → bot ≤ Q → ∀ ζ, ζ < Q → LeCl (Om (1 + 1)) Q (g ζ)
  clmh : ∀ Q, SC Q → both ≤ Q → ∀ v, v < Q → LeCl (Om 1) Q (gh v)
  sth : StrictMono gh
  cont : ∀ v, IsSuccLimit v → ∀ u, u < gh v → ∃ v', v' < v ∧ u < gh v'
  memS : ∀ c, bot ≤ c → gs ∈ S.CSet 0 c
  memhS : ∀ c, both ≤ c → ghs ∈ S.CSet 0 c
  clS : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q gs
  clhS : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q ghs

/-- A shape stays valid above larger bottoms. -/
theorem scShp_mono {l bot both bot' both' : Ordinal.{0}} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}}
    (h : ScShp S l g gh gs ghs bot both) (hb : bot ≤ bot') (hbh : both ≤ both') :
    ScShp S l g gh gs ghs bot' both' :=
  ⟨h.st, h.lt, h.lth, h.inf, h.infh, h.hull, h.hullS, fun x c hx hc => h.mem x c hx (hb.trans hc),
    fun v c hv hc => h.memh v c hv (hbh.trans hc), fun Q hQ hc => h.cl Q hQ (hb.trans hc),
    fun Q hQ hc => h.clh Q hQ (hbh.trans hc), h.idx, fun Q hQ hc => h.clm Q hQ (hb.trans hc),
    fun Q hQ hc => h.clmh Q hQ (hbh.trans hc), h.sth, h.cont, fun c hc => h.memS c (hb.trans hc),
    fun c hc => h.memhS c (hbh.trans hc), fun Q hQ hc => h.clS Q hQ (hb.trans hc),
    fun Q hQ hc => h.clhS Q hQ (hbh.trans hc)⟩

section Lift

variable {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs Q : Ordinal.{0}}

/-- **The closure law passes from `g` to `W^g`.** -/
theorem scShCl_lift (hQ : SC Q) (hinf : ω ≤ gs) (h : ScShCl g gs Q) :
    ScShCl (fun z => leWe (g z)) (leWe gs) Q := by
  intro w hw hlt
  have e : Om (1 + 1 : Ordinal.{0}) * leWe gs = leWe gs := by
    rw [rvWe_mul, Ordinal.one_add_of_omega0_le hinf]
  rw [e] at hlt
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨0, hQ.1, mul_pos ldOm2_SC.1 (leWe_pos _)⟩
  have hlog : log ω w < Om (1 + 1) * gs :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hw0).trans_lt hlt)
  obtain ⟨-, hlC⟩ := leClDec hQ ldOm2_SC w hw
  obtain ⟨ζ, hζQ, hζ⟩ := h _ hlC hlog
  refine ⟨ζ, hζQ, ?_⟩
  have h1 := lt_opow_succ_log_self one_lt_omega0 w
  rw [Order.succ_eq_add_one] at h1
  exact (h1.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hζ))).trans_le
    (Ordinal.le_mul_right _ ldOm2_SC.1)

/-- **The image closure law passes from `ĝ` to `Ω^ĝ`.** -/
theorem scImCl_lift (hQ : SC Q) (hinf : ω ≤ ghs) (h : ScImCl gh ghs Q) :
    ScImCl (fun v => leOe (gh v)) (leOe ghs) Q := by
  intro w hw hlt
  rw [rwO_mul_Oe hinf] at hlt
  rcases eq_or_ne w 0 with rfl | hw0
  · exact ⟨0, hQ.1, mul_pos (Om_pos one_ne_zero) (leOe_pos _)⟩
  have hlog : log ω w < Om 1 * ghs :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hw0).trans_lt hlt)
  obtain ⟨-, hlC⟩ := leClDec hQ Ph.ph_SC_Om1 w hw
  obtain ⟨v, hvQ, hv⟩ := h _ hlC hlog
  refine ⟨v, hvQ, ?_⟩
  have h1 := lt_opow_succ_log_self one_lt_omega0 w
  rw [Order.succ_eq_add_one] at h1
  exact (h1.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hv))).trans_le
    (Ordinal.le_mul_right _ (Om_pos one_ne_zero))

/-- **The base closure law** (`g ζ = ζ`, `g* = Ω₂`). -/
theorem scShCl_code (hQ : SC Q) : ScShCl (fun z => z) (Om (1 + 1)) Q := by
  intro w hw hlt
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have e : ω ^ (Om (1 + 1 : Ordinal.{0}) * 1 + Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
    rw [mul_one, opow_add, gg_SC_eps ldOm2_SC]
  have hb := leCl_boundY hQ ldOm2_SC (LeCl.small (gg_one_lt_of_SC hQ)) _ hw (by rw [e]; exact hlt)
  rw [mul_one, gg_SC_eps ldOm2_SC] at hb
  have hq : w / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt hW0).1 hb
  refine ⟨w / Om (1 + 1) + 1, hQ.isSuccLimit.succ_lt hq, ?_⟩
  calc w < Om (1 + 1) * (w / Om (1 + 1)) + Om (1 + 1) := Ordinal.lt_mul_div_add _ hW0
    _ = Om (1 + 1) * (w / Om (1 + 1) + 1) := (mul_add_one _ _).symm

/-- **The base image closure law** (`ĝ v = v`, `ĝ* = Ω₁`). -/
theorem scImCl_code (hQ : SC Q) : ScImCl (fun v => v) (Om 1) Q := by
  intro w hw hlt
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have e : ω ^ (Om (1 : Ordinal.{0}) * 1 + Om 1) = Om 1 * Om 1 := by
    rw [mul_one, opow_add, gg_SC_eps Ph.ph_SC_Om1]
  have hb := leCl_boundY hQ Ph.ph_SC_Om1 (LeCl.small (gg_one_lt_of_SC hQ)) _ hw (by rw [e]; exact hlt)
  rw [mul_one, gg_SC_eps Ph.ph_SC_Om1] at hb
  have hq : w / Om 1 < Q := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hb
  exact ⟨w / Om 1, hq, Ordinal.lt_mul_div_add _ hΩ0 |>.trans_le (by rw [mul_add_one])⟩

end Lift

section Idx

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The index passes from `g` to `W^g`.** -/
theorem scIdx_lift {g : Ordinal.{0} → Ordinal.{0}} {gs : Ordinal.{0}}
    (h : ∀ c, c ∈ cdHull S l → c < gs → ∃ q, GxCl (upsilon l) (ldAtR S l) q ∧ q < Om (1 + 1) ∧
      c < g (q + 1) ∧ (q ≠ 0 → g q ≤ c)) :
    ∀ r, r ∈ cdHull S l → r < leWe gs → ∃ q, GxCl (upsilon l) (ldAtR S l) q ∧ q < Om (1 + 1) ∧
      r < leWe (g (q + 1)) ∧ (q ≠ 0 → leWe (g q) ≤ r) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  intro r hr hlt
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, GxCl.zero hρSC.1, ldOm2_SC.1, leWe_pos _, fun h => absurd rfl h⟩
  have hlog : log ω r < Om (1 + 1) * gs :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hlt)
  set c := log ω r / Om (1 + 1) with hc_def
  have hcH : c ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hr)
  have hcg : c < gs := (Ordinal.lt_mul_iff_div_lt hW0).1 hlog
  obtain ⟨q, hq, hqW, hcq, hgq⟩ := h c hcH hcg
  have hrc := roLt_We_log r
  rw [← hc_def] at hrc
  have hWc : leWe c ≤ r := by
    unfold leWe
    exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hr0)
  exact ⟨q, hq, hqW, hrc.trans_le (leWe_mono (Order.add_one_le_of_lt hcq)),
    fun h0 => (leWe_mono (hgq h0)).trans hWc⟩

/-- **The base shape**: codes `ζ < Ω₂` with the images `Θ ζ`, top `Ω₂` (image `Ω₁`), at every bottom. -/
theorem scShp_code (bot both : Ordinal.{0}) :
    ScShp S l (fun z => z) (fun v => v) (Om (1 + 1)) (Om 1) bot both := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  refine ⟨strictMono_id, fun _ h => h, fun _ h => h, (Lw.lw_omega_lt_SC ldOm2_SC).le,
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le, fun ζ hζ hζW => (ldHull_iff hl hX hζW).2 hζ, mxOm2_mem _ _,
    fun _ _ h _ => h, fun _ _ h _ => h, fun Q hQ _ => scShCl_code hQ, fun Q hQ _ => scImCl_code hQ, ?_,
    fun Q _ _ ζ hζ => LeCl.small hζ, fun Q _ _ v hv => LeCl.small hv, strictMono_id,
    fun v hv u hu => ⟨u + 1, hv.succ_lt hu, lt_add_one u⟩, fun c _ => mxOm2_mem _ _,
    fun c _ => CSet.Om_mem (CSet.one_mem _ _), fun Q _ _ => LeCl.om, fun Q _ _ => LeCl.om⟩
  intro c hcH hc
  exact ⟨c, (ldHull_iff hl hX hc).1 hcH, hc, lt_add_one c, fun _ => le_rfl⟩

end Idx

section Step

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop}
  (hshp : ∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
    (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b)))
  (hmono : ∀ b β X0, Ow b X0 → b ≤ β → Ow β X0)
  (hmem : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
    ScLev S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
      (gh (gxTh (upsilon l) (ldAtR S l) ζ)))

include hl hX hshp hmono hmem

/-- **THE LEVEL STEP: the members of a shape give its limit exponent**, at every level. -/
theorem scLev_om : ScLev S l Ow gs ghs := by
  intro b X0 Xh0 hoffb hd hG3 hG hOw β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have hoff := rvOff_mono hbβ hoffb
  have hOwβ := hmono _ _ _ hOw hbβ
  have hsh := hshp _ _ hOwβ
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb
  rw [add_zero] at hβd hβown
  have hst : StrictMono (fun z => leWe (g z)) := fun a b h => leWe_lt (hsh.st h)
  have hlt : ∀ x, x < Om (1 + 1) → leWe (g x) < leWe gs := fun x hx => leWe_lt (hsh.lt x hx)
  have hG3' : X0 + leWe gs < S.psi 0 (Om (1 + 1 + 1)) := le_self_add.trans_lt hG3
  have hbot : leTe S (X0 + leWe (g 1)) β ≤ S.psi (β + leWe (X0 + leWe (g (Om 1)))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2
      (leWe_mono (hsh.st.monotone (Order.one_le_iff_pos.2 (Om_pos one_ne_zero)))))))).1
  have hGm : ∀ x c, x ∈ S.CSet 0 c → leTe S (X0 + leWe (g 1)) β ≤ c → leWe (g x) ∈ S.CSet 0 c :=
    fun x c hx hc => leWe_mem (hsh.mem x c hx hc)
  have hcl : ∀ Q, SC Q → leTe S (X0 + leWe (g 1)) β ≤ Q → ScShCl (fun z => leWe (g z)) (leWe gs) Q :=
    fun Q hQ hc => scShCl_lift hQ hsh.inf (hsh.cl Q hQ hc)
  refine scOmTop hl hX hst hlt (fun v hv => leOe_lt (hsh.lth v hv)) hoff hb' hÂ hbase
    (fun ζ hζ hζW => leWe_mem (hsh.hull ζ hζ hζW)) hGm hcl hG3' ?_ rfl
    (fun v c hv hc => leOe_mem (hsh.memh v c hv hc))
    (fun Q hQ hc => scImCl_lift hQ hsh.infh (hsh.clh Q hQ hc))
    (scIdx_lift hl hX hsh.idx) (le_self_add.trans_lt hG) (leWe_mem hsh.hullS) hd
  intro ζ hζ h1 hζT hΘ1
  have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
  obtain ⟨j, hj⟩ := scSq_sup hst (fun x hx => (hlt x hx).le) hβown hX0m
    (fun x c hx hc => hGm x c hx (hbot.trans hc)) (fun Q hQ hc => hcl Q hQ (hbot.trans hc)) hβd hX0cl hG3' hζT
  have hgle : g ζ ≤ gs := (hsh.lt ζ hζW).le
  have ht := hmem ζ hζ h1 hζW β X0 Xh0 hoff ((leWe_dvd hgle).trans hd)
    (lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hgle)) _) hG3)
    (lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono (hsh.lth _ hΘ1).le)) _) hG)
    ⟨hOwβ, j, hj⟩
  have e1 := ht β Â (roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (leWe_mono hgle))
    zero_le) le_rfl hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at e1
  exact e1

end Step

/-- `SQ` of the lifted base shape `ζ ↦ W^ζ` is `Rw.rwEX`. -/
theorem scSq_code (X0 β : Ordinal.{0}) : ∀ j, scSq S (fun z => leWe z) X0 β j = rwEX S X0 β j
  | 0 => rfl
  | j + 1 => by
    change S.psi (β + leWe (X0 + leWe (scSq S (fun z => leWe z) X0 β j))) (Om (1 + 1)) =
      S.psi (β + leWe (X0 + leWe (rwEX S X0 β j))) (Om (1 + 1))
    rw [scSq_code X0 β j]

section W

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `W^{Ω₂}` over every offset and base bound** (image `Ω^{Ω₁}`): `ScLev ⊤ Ω₂ Ω₁`, i.e.
`Θ(ψ_{Ω₂}(β + W^{X₀ + W^{Ω₂}})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Ω₁}})` (the offset version of `Rw.rwTopWW`). -/
theorem scLev_W : ScLev S l (fun _ _ => True) (Om (1 + 1)) (Om 1) := by
  refine scLev_om (g := fun z => z) (gh := fun v => v) hl hX
    (fun b X0 _ => scShp_code hl hX _ _) (fun _ _ _ _ _ => trivial) ?_
  intro ζ hζ h1 hζW b X0 Xh0 hoff hd hG3 hG hOw
  obtain ⟨-, j, hj⟩ := hOw
  rw [scSq_code] at hj
  exact rwLevC_all hl hX ζ hζ h1 hζW b X0 Xh0 hoff hd hG3 hG ⟨j, hj⟩

end W

end Googology.Trans.PoR.InaccPsi.R2.Sc
