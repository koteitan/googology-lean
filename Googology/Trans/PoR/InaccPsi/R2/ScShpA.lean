import Googology.Trans.PoR.InaccPsi.R2.ScShp

/-!
# The algebra of shapes: lift, prefix, linear

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`.  Every limit exponent `E < ε_{Ω₂+1}` that is a limit of `Ω₂` members has a shape built
from three constructors (`Sc.ScShp`), each keeping all the fields (closure laws, index, membership, `LeCl`):
* `scShp_lift`: `ζ ↦ W^{g ζ}` (top `W^{g*}`, image `v ↦ Ω^{ĝ v}`, top `Ω^{ĝ*}`), the next level over a shape;
* `scShp_pre`: `ζ ↦ E₀ + g ζ` (top `E₀ + g*`, image `Ê₀ + ĝ v`), for a constant `E₀` own above the bottom with
  `g* ∣ E₀`, `g* = ω^k`;
* `scShp_lin`: `ζ ↦ W^F·ζ` (top `W^{F+1}`, image `v ↦ Ω^{F̂}·v`, top `Ω^{F̂+1}`), for `F` own above the bottom.
The base shape `ζ ↦ ζ` (`Sc.scShp_code`) is `scShp_lin` at `F = 0`.  So the shape of `E₀ + W^{F+1}` is
`pre E₀ (lin F)` and the shape of `E₀ + W^{F*}` (`F*` a limit of `Ω₂` members with shape `h`) is `pre E₀ (lift h)`:
**a shape of one level gives the shape of the next** (`scShp_lift`), at every level.

* `scShp_lift`, `scShCl_pre`, `scImCl_pre`, `scShp_pre`, `scShCl_lin`, `scImCl_lin`, `scShp_lin`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

theorem scOmega_le_We {x : Ordinal.{0}} (hx : 0 < x) : ω ≤ leWe x := by
  have h : (1 : Ordinal.{0}) ≤ Om (1 + 1) * x := Order.one_le_iff_pos.2 (mul_pos ldOm2_SC.1 hx)
  calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ leWe x := opow_le_opow_right omega0_pos h

theorem scOmega_le_Oe {x : Ordinal.{0}} (hx : 0 < x) : ω ≤ leOe x := by
  have h : (1 : Ordinal.{0}) ≤ Om 1 * x := Order.one_le_iff_pos.2 (mul_pos (Om_pos one_ne_zero) hx)
  calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ leOe x := opow_le_opow_right omega0_pos h

/-- **The value of a continuous strictly monotone map at a limit is a limit.** -/
theorem scLim_of_cont {gh : Ordinal.{0} → Ordinal.{0}} (hst : StrictMono gh)
    (hc : ∀ v, IsSuccLimit v → ∀ u, u < gh v → ∃ v', v' < v ∧ u < gh v') {v : Ordinal.{0}} (hv : IsSuccLimit v) :
    IsSuccLimit (gh v) := by
  rcases zero_or_succ_or_isSuccLimit (gh v) with h0 | ⟨w, hw⟩ | h
  · have := hst (pos_iff_ne_zero.2 hv.ne_bot); rw [h0] at this; exact absurd this (not_lt.2 zero_le)
  · rw [succ_eq_add_one] at hw
    obtain ⟨v', hv', hw'⟩ := hc v hv w (by rw [← hw]; exact lt_add_one w)
    have h1 := hst hv'
    rw [← hw] at h1
    exact absurd (Order.add_one_le_of_lt hw') (not_le.2 h1)
  · exact h

section Cons

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs bot both : Ordinal.{0}}

include hl hX in
/-- **The lift `ζ ↦ W^{g ζ}`: a shape of one level gives the shape of the next.** -/
theorem scShp_lift (h : ScShp S l g gh gs ghs bot both) :
    ScShp S l (fun z => leWe (g z)) (fun v => leOe (gh v)) (leWe gs) (leOe ghs) bot both := by
  have hgs0 : 0 < gs := omega0_pos.trans_le h.inf
  have hghs0 : 0 < ghs := omega0_pos.trans_le h.infh
  refine ⟨fun a b hab => leWe_lt (h.st hab), fun ζ hζ => leWe_lt (h.lt ζ hζ), fun v hv => leOe_lt (h.lth v hv),
    scOmega_le_We hgs0, scOmega_le_Oe hghs0, fun ζ hζ hζW => leWe_mem (h.hull ζ hζ hζW), leWe_mem h.hullS,
    fun x c hx hc => leWe_mem (h.mem x c hx hc), fun v c hv hc => leOe_mem (h.memh v c hv hc),
    fun Q hQ hc => scShCl_lift hQ h.inf (h.cl Q hQ hc), fun Q hQ hc => scImCl_lift hQ h.infh (h.clh Q hQ hc),
    scIdx_lift hl hX h.idx,
    fun Q hQ hc ζ hζ => LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (h.clm Q hQ hc ζ hζ)),
    fun Q hQ hc v hv => LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (h.clmh Q hQ hc v hv)),
    fun a b hab => leOe_lt (h.sth hab), fun v hv u hu => ?_, fun c hc => leWe_mem (h.memS c hc),
    fun c hc => leOe_mem (h.memhS c hc), fun Q hQ hc => LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (h.clS Q hQ hc)),
    fun Q hQ hc => LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (h.clhS Q hQ hc))⟩
  obtain ⟨e', -, he', hue'⟩ := rvLt_Oe_lim (scLim_of_cont h.sth h.cont hv) hu
  obtain ⟨v', hv', he'v⟩ := h.cont v hv e' he'
  exact ⟨v', hv', hue'.trans (leOe_lt he'v)⟩

end Cons

section Pre

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs Q E0 Eh0 : Ordinal.{0}}

theorem scShCl_pre (hQ : SC Q) (hE0 : LeCl (Om (1 + 1)) Q E0) (h : ScShCl g gs Q) :
    ScShCl (fun z => E0 + g z) (E0 + gs) Q := by
  intro w hw hlt
  rcases lt_or_ge w (Om (1 + 1) * E0) with h1 | h1
  · exact ⟨0, hQ.1, h1.trans_le (by rw [mul_add]; exact le_self_add)⟩
  have hC := (leClDec hQ ldOm2_SC w hw).1 _ (LeCl.mulK hQ ldOm2_SC E0 hE0) h1
  have hdec : Om (1 + 1) * E0 + (w - Om (1 + 1) * E0) = w := Ordinal.add_sub_cancel_of_le h1
  have hu : w - Om (1 + 1) * E0 < Om (1 + 1) * gs := by
    have : Om (1 + 1) * E0 + (w - Om (1 + 1) * E0) < Om (1 + 1) * E0 + Om (1 + 1) * gs := by
      rw [hdec, ← mul_add]; exact hlt
    exact (add_lt_add_iff_left _).1 this
  obtain ⟨ζ, hζQ, hζ⟩ := h _ hC hu
  refine ⟨ζ, hζQ, ?_⟩
  rw [mul_add, ← hdec]; exact (add_lt_add_iff_left _).2 hζ

theorem scImCl_pre (hQ : SC Q) (hE0 : LeCl (Om 1) Q Eh0) (h : ScImCl gh ghs Q) :
    ScImCl (fun v => Eh0 + gh v) (Eh0 + ghs) Q := by
  intro w hw hlt
  rcases lt_or_ge w (Om 1 * Eh0) with h1 | h1
  · exact ⟨0, hQ.1, h1.trans_le (by rw [mul_add]; exact le_self_add)⟩
  have hC := (leClDec hQ Ph.ph_SC_Om1 w hw).1 _ (LeCl.mulK hQ Ph.ph_SC_Om1 Eh0 hE0) h1
  have hdec : Om 1 * Eh0 + (w - Om 1 * Eh0) = w := Ordinal.add_sub_cancel_of_le h1
  have hu : w - Om 1 * Eh0 < Om 1 * ghs := by
    have : Om 1 * Eh0 + (w - Om 1 * Eh0) < Om 1 * Eh0 + Om 1 * ghs := by
      rw [hdec, ← mul_add]; exact hlt
    exact (add_lt_add_iff_left _).1 this
  obtain ⟨v, hvQ, hv⟩ := h _ hC hu
  refine ⟨v, hvQ, ?_⟩
  rw [mul_add, ← hdec]; exact (add_lt_add_iff_left _).2 hv

variable {bot both k : Ordinal.{0}}

include hl hX in
/-- **The prefix `ζ ↦ E₀ + g ζ`** for a constant `E₀` own above the bottom. -/
theorem scShp_pre (h : ScShp S l g gh gs ghs bot both) (hE0H : E0 ∈ cdHull S l)
    (hE0m : E0 ∈ S.CSet 0 bot) (hEh0m : Eh0 ∈ S.CSet 0 both)
    (hE0cl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q E0) (hEh0cl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q Eh0)
    (hk : gs = ω ^ k) (hdv : gs ∣ E0) :
    ScShp S l (fun z => E0 + g z) (fun v => Eh0 + gh v) (E0 + gs) (Eh0 + ghs) bot both := by
  refine ⟨fun a b hab => (add_lt_add_iff_left E0).2 (h.st hab),
    fun ζ hζ => (add_lt_add_iff_left E0).2 (h.lt ζ hζ), fun v hv => (add_lt_add_iff_left Eh0).2 (h.lth v hv),
    h.inf.trans le_add_self, h.infh.trans le_add_self,
    fun ζ hζ hζW => CSet.add_mem hE0H (h.hull ζ hζ hζW), CSet.add_mem hE0H h.hullS,
    fun x c hx hc => CSet.add_mem (CSet_mono le_rfl hc hE0m) (h.mem x c hx hc),
    fun v c hv hc => CSet.add_mem (CSet_mono le_rfl hc hEh0m) (h.memh v c hv hc),
    fun Q hQ hc => scShCl_pre hQ (hE0cl Q hQ hc) (h.cl Q hQ hc),
    fun Q hQ hc => scImCl_pre hQ (hEh0cl Q hQ hc) (h.clh Q hQ hc), ?_,
    fun Q hQ hc ζ hζ => LeCl.add (hE0cl Q hQ hc) (h.clm Q hQ hc ζ hζ),
    fun Q hQ hc v hv => LeCl.add (hEh0cl Q hQ hc) (h.clmh Q hQ hc v hv),
    fun a b hab => (add_lt_add_iff_left Eh0).2 (h.sth hab), fun v hv u hu => ?_,
    fun c hc => CSet.add_mem (CSet_mono le_rfl hc hE0m) (h.memS c hc),
    fun c hc => CSet.add_mem (CSet_mono le_rfl hc hEh0m) (h.memhS c hc),
    fun Q hQ hc => LeCl.add (hE0cl Q hQ hc) (h.clS Q hQ hc), fun Q hQ hc => LeCl.add (hEh0cl Q hQ hc) (h.clhS Q hQ hc)⟩
  swap
  · rcases lt_or_ge u Eh0 with h1 | h1
    · exact ⟨0, pos_iff_ne_zero.2 hv.ne_bot, h1.trans_le le_self_add⟩
    obtain ⟨u', rfl⟩ := exists_add_of_le h1
    obtain ⟨v', hv', hu'⟩ := h.cont v hv u' ((add_lt_add_iff_left Eh0).1 hu)
    exact ⟨v', hv', (add_lt_add_iff_left Eh0).2 hu'⟩
  intro c hcH hc
  rcases lt_or_ge c E0 with h1 | h1
  · exact ⟨0, GxCl.zero (leRho hl hX).1.1, ldOm2_SC.1, h1.trans_le le_self_add, fun h0 => absurd rfl h0⟩
  obtain ⟨c', rfl⟩ := exists_add_of_le h1
  have hc' : c' < gs := (add_lt_add_iff_left E0).1 hc
  have hc'H : c' ∈ cdHull S l := by
    have h2 := leModP_mem (S := S) k hcH
    have hm : (E0 + c') % ω ^ k = c' := by
      obtain ⟨q', hq'⟩ := hdv
      rw [← hk, hq', Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc']
    rwa [hm] at h2
  obtain ⟨q, hq, hqW, hcq, hgq⟩ := h.idx c' hc'H hc'
  exact ⟨q, hq, hqW, (add_lt_add_iff_left E0).2 hcq, fun h0 => (add_le_add_iff_left E0).2 (hgq h0)⟩

end Pre

section Lin

variable {Q F Fh : Ordinal.{0}}

theorem scShCl_lin (hQ : SC Q) (hF : LeCl (Om (1 + 1)) Q F) :
    ScShCl (fun z => leWe F * z) (leWe (F + 1)) Q := by
  intro w hw hlt
  have hK0 : leWe (1 + F) ≠ 0 := (leWe_pos _).ne'
  have e : Om (1 + 1) * leWe (F + 1) = ω ^ (Om (1 + 1) * (1 + F) + Om (1 + 1)) := by
    rw [rvWe_mul, ← add_assoc]; unfold leWe; rw [mul_add_one]
  rw [e] at hlt
  have h1F : LeCl (Om (1 + 1)) Q (1 + F) := LeCl.add (LeCl.small (gg_one_lt_of_SC hQ)) hF
  have hb := leCl_boundY hQ ldOm2_SC h1F _ hw hlt
  change _ < leWe (1 + F) * Q at hb
  have hq : w / leWe (1 + F) < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
  refine ⟨w / leWe (1 + F) + 1, hQ.isSuccLimit.succ_lt hq, ?_⟩
  rw [← mul_assoc, rvWe_mul F]
  calc w < leWe (1 + F) * (w / leWe (1 + F)) + leWe (1 + F) := Ordinal.lt_mul_div_add _ hK0
    _ = leWe (1 + F) * (w / leWe (1 + F) + 1) := (mul_add_one _ _).symm

theorem scImCl_lin (hQ : SC Q) (hF : LeCl (Om 1) Q Fh) :
    ScImCl (fun v => leOe Fh * v) (leOe (Fh + 1)) Q := by
  intro w hw hlt
  have hK0 : leOe (1 + Fh) ≠ 0 := (leOe_pos _).ne'
  have e : Om 1 * leOe (Fh + 1) = ω ^ (Om 1 * (1 + Fh) + Om 1) := by
    rw [rvOe_mul, ← add_assoc]; unfold leOe; rw [mul_add_one]
  rw [e] at hlt
  have h1F : LeCl (Om 1) Q (1 + Fh) := LeCl.add (LeCl.small (gg_one_lt_of_SC hQ)) hF
  have hb := leCl_boundY hQ Ph.ph_SC_Om1 h1F _ hw hlt
  change _ < leOe (1 + Fh) * Q at hb
  have hq : w / leOe (1 + Fh) < Q := (Ordinal.lt_mul_iff_div_lt hK0).1 hb
  refine ⟨w / leOe (1 + Fh), hq, ?_⟩
  rw [← mul_assoc, rvOe_mul Fh]
  calc w < leOe (1 + Fh) * (w / leOe (1 + Fh)) + leOe (1 + Fh) := Ordinal.lt_mul_div_add _ hK0
    _ = leOe (1 + Fh) * (w / leOe (1 + Fh) + 1) := (mul_add_one _ _).symm

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {bot both : Ordinal.{0}}

include hl hX in
/-- **The linear shape `ζ ↦ W^F·ζ`** (top `W^{F+1}`, image `v ↦ Ω^{F̂}·v`) for `F` own above the bottom. -/
theorem scShp_lin (hFH : F ∈ cdHull S l) (hFm : F ∈ S.CSet 0 bot) (hFhm : Fh ∈ S.CSet 0 both)
    (hFcl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q F) (hFhcl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q Fh) :
    ScShp S l (fun z => leWe F * z) (fun v => leOe Fh * v) (leWe (F + 1)) (leOe (Fh + 1)) bot both := by
  have hk0 : leWe F ≠ 0 := (leWe_pos F).ne'
  refine ⟨fun a b hab => leMulWe_lt hab, fun ζ hζ => rvWe_lt_succ hζ, fun v hv => rvOe_lt_succ hv,
    scOmega_le_We (lt_add_one F |>.trans_le' zero_le), scOmega_le_Oe (lt_add_one Fh |>.trans_le' zero_le),
    fun ζ hζ hζW => leMulWe_mem hFH ((ldHull_iff hl hX hζW).2 hζ), leWe_mem (CSet.succ_mem hFH),
    fun x c hx hc => leMulWe_mem (CSet_mono le_rfl hc hFm) hx,
    fun v c hv hc => leMulOe_mem (CSet_mono le_rfl hc hFhm) hv,
    fun Q hQ hc => scShCl_lin hQ (hFcl Q hQ hc), fun Q hQ hc => scImCl_lin hQ (hFhcl Q hQ hc), ?_,
    fun Q hQ hc ζ hζ => rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC F (hFcl Q hQ hc)) ldOm2_SC _ (LeCl.small hζ),
    fun Q hQ hc v hv => rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 Fh (hFhcl Q hQ hc)) Ph.ph_SC_Om1 _
      (LeCl.small hv), fun a b hab => (mul_lt_mul_iff_right₀ (leOe_pos Fh)).2 hab, fun v hv u hu => ?_,
    fun c hc => leWe_mem (CSet.succ_mem (CSet_mono le_rfl hc hFm)),
    fun c hc => leOe_mem (CSet.succ_mem (CSet_mono le_rfl hc hFhm)),
    fun Q hQ hc => LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (LeCl.add (hFcl Q hQ hc) (LeCl.small (gg_one_lt_of_SC hQ)))),
    fun Q hQ hc => LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _
      (LeCl.add (hFhcl Q hQ hc) (LeCl.small (gg_one_lt_of_SC hQ))))⟩
  swap
  · have hO0 : leOe Fh ≠ 0 := (leOe_pos Fh).ne'
    have hq : u / leOe Fh < v := (Ordinal.lt_mul_iff_div_lt hO0).1 hu
    refine ⟨u / leOe Fh + 1, hv.succ_lt hq, ?_⟩
    calc u < leOe Fh * (u / leOe Fh) + leOe Fh := Ordinal.lt_mul_div_add _ hO0
      _ = leOe Fh * (u / leOe Fh + 1) := (mul_add_one _ _).symm
  intro c hcH hc
  have hcW : c < ω ^ (Om (1 + 1) * F + Om (1 + 1)) := by
    have e : leWe (F + 1) = ω ^ (Om (1 + 1) * F + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← e]; exact hc
  have hqH : c / leWe F ∈ cdHull S l := leDivOp_mem (dvd_mul_right _ _) hcH hcW
  have hqW : c / leWe F < Om (1 + 1) := by
    rw [leWe_succ] at hc; exact (Ordinal.lt_mul_iff_div_lt hk0).1 hc
  refine ⟨c / leWe F, (ldHull_iff hl hX hqW).1 hqH, hqW, ?_, fun _ => Ordinal.mul_div_le _ _⟩
  calc c < leWe F * (c / leWe F) + leWe F := Ordinal.lt_mul_div_add _ hk0
    _ = leWe F * (c / leWe F + 1) := (mul_add_one _ _).symm

end Lin

end Googology.Trans.PoR.InaccPsi.R2.Sc
