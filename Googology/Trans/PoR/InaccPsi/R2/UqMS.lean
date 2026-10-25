import Googology.Trans.PoR.InaccPsi.R2.UqStep

/-!
# Member systems past `Γ₂` with the bound `Y₃`: the composite exponents

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`C_k(Q) = Ug.UgC S k Q`, `Γ₂ = Ua.uaGam`, `Y₃ = ψ_{Ω₃}(Ω₃)`, member systems `Uq.UqMA`, `Uq.UqMB`.

* `uqMA_of_ua`, `uqMB_of_ua` (**below `Γ₂` the member systems of `Ua` are member systems past `Γ₂`**: `T = Ua.uaTh`
  there and the level codes below `Γ₂` are the codes `LeCl Ω₂`, `Ug.ugC_toLe`, `Um.umC1_toLe`);
* `uqRangeX`, `uqMA_coef` (`e + W^f·c`, `c` a limit code), `uqMB_succ` (`e + W^{f+1}`), `uqMA_lift`, `uqMB_lift`
  (`e + W^f` from the members of `f`): `Ua.uaMA_coef`, `Ua.uaMB_succ`, `Ua.uaMA_lift`, `Ua.uaMB_lift` with the image
  `T`, the level codes and the bound `Y₃` (`Ug.ugAddT`, `Ug.ugAddW`, `Ug.ugSucc`, `Ug.ugDvd`);
* `UqFixMS` (**the member systems at the `W`-fixed limits `Γ₂ ≤ r < B` of `H_λ`, given those of the smaller limits**);
* `uqMS` (**EVERY LIMIT EXPONENT `e + r < B ≤ Y₃` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM, given
  `UqFixMS S λ B`**:
  the `W`-fixed limits below `Γ₂` by `Ud.udMS`, the composite ones by the four lemmas above).

No new axiom.  New definition: `UqFixMS`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Um

variable {S : InaccSeq.{0}}

/-- **Below `Γ₂` countable members of `Ua` are members past `Γ₂`.** -/
theorem uqMA_of_ua {l E : Ordinal.{0}} (hEG : E < uaGam) (h : UaMA S l E) : UqMA S l E := by
  obtain ⟨Mem, hdat, hne, hA1, hA2, hA3⟩ := h
  refine ⟨Mem, hdat, hne, hA1, ?_, ?_⟩
  · intro z hz
    rw [ugTh_lt hEG] at hz
    obtain ⟨m, hm, hzm⟩ := hA2 z hz
    exact ⟨m, hm, by rw [ugTh_lt ((hdat m hm).2.2.trans hEG)]; exact hzm⟩
  · intro Q hQ m h hm h1 h2 hh
    exact UgC.of_le (hA3 Q hQ m h hm h1 h2 (ugC_toLe hh (h2.trans_lt hEG)))

/-- The part `e + W^f·c'` of a level-2 code `h ∈ [e + W^f·c', e + W^f·c]` is a code. -/
theorem uqRangeX {Q e f c c' h : Ordinal.{0}} (hQ : SC Q) (hd : leWe (f + 1) ∣ e) (hcW : c < Om (1 + 1))
    (hc1 : 1 ≤ c') (h1 : e + leWe f * c' ≤ h) (h2 : h ≤ e + leWe f * c) (hh : UgC S (1 + 1) Q h) :
    UgC S (1 + 1) Q (e + leWe f * c') := by
  have hdE : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans h1 : e ≤ h)
  have hx1 : leWe f * c' ≤ x := (add_le_add_iff_left e).1 h1
  have hx2 : x ≤ leWe f * c := (add_le_add_iff_left e).1 h2
  set c'' := x / leWe f with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.mul_le_iff_le_div (leWe_pos f).ne').1 hx1
  have hc''W : c'' < Om (1 + 1) := hc''c.trans_lt hcW
  have ex : e + x = e + leWe f * c'' + x % leWe f := by rw [add_assoc, Ordinal.div_add_mod]
  rw [ex] at hh
  have hP' : UgC S (1 + 1) Q (e + leWe f * c'') := by
    rcases eq_or_ne (x % leWe f) 0 with h0 | h0
    · rwa [h0, add_zero] at hh
    have hdv : leWe f ∣ e + leWe f * c'' := dvd_add hdE (dvd_mul_right _ _)
    have k1 : e + leWe f * c'' + leWe 0 ≤ e + leWe f * c'' + x % leWe f := by
      rw [leWe_zero]; exact (add_le_add_iff_left _).2 (Order.one_le_iff_ne_zero.2 h0)
    have k2 : e + leWe f * c'' + x % leWe f ≤ e + leWe f * c'' + leWe f :=
      (add_le_add_iff_left _).2 (Ordinal.mod_lt _ (leWe_pos f).ne').le
    exact (uqHeadE hQ hdv k1 k2 hh).1
  obtain ⟨hP, hfc, hc''Q⟩ := uqCodeHeadX hQ hd (hc1.trans hc'c'') hc''W hP'
  exact UgC.add hP (uqMulW hQ hfc (UgC.small (hc'c''.trans_lt hc''Q)))

/-- **The member systems at the `W`-fixed limits `Γ₂ ≤ r < B` of `H_λ`**, given those of the smaller limits. -/
def UqFixMS (S : InaccSeq.{0}) (l B : Ordinal.{0}) : Prop :=
  ∀ r, r ∈ cdHull S l → uaGam ≤ r → r < B → ¬ sgLW r < r →
    (∀ r', r' ∈ cdHull S l → IsSuccLimit r' → r' < r → UqMA S l r' ∨ UqMB S l r') → UqMA S l r ∨ UqMB S l r

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Below `Γ₂` members of `Ua` indexed by the codes are members past `Γ₂`.** -/
theorem uqMB_of_ua {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hEG : E < uaGam) (h : UaMB S l E) : UqMB S l E := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := h
  have hTE : ugTh S l E = uaTh S l E := ugTh_lt hEG
  refine ⟨M, Mh, hM, hMh, ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    obtain ⟨a1, a2, a3, a4, a5⟩ := hB0 c hc hc1 hcW
    exact ⟨a1, a2, a3, by rw [ugTh_lt (a3.trans hEG)]; exact a4, by rw [hTE]; exact a5⟩
  · intro Q hQ hQ1 w hw hwE
    exact hB1 Q hQ hQ1 w (ugC_toLe hw (hwE.trans hEG)) hwE
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    exact hB2 Q hQ w (umC1_toLe hw (hwE.trans (uaLtG1 hl hX E hEH hEG))) hwE
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    exact UgC.of_le (hB3 Q hQ c h hc1 hcQ h1 h2 (ugC_toLe hh (h2.trans_lt hEG)))

/-- **`e + W^f·c`, `c` a limit code** (`W^{f+1} ∣ e`, `< Y₃`): countable members `e + W^f·c'`. -/
theorem uqMA_coef {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hlim : IsSuccLimit c) (hcW : c < Om (1 + 1))
    (hd : leWe (f + 1) ∣ e) (hlt : e + leWe f * c < ugY S) :
    UqMA S l (e + leWe f * c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
  have hmlt : ∀ c', c' < c → e + leWe f * c' < e + leWe f * c := fun c' h =>
    (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left h (leWe_pos f))
  have hT : ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' ≤ c →
      ugTh S l (e + leWe f * c') = ugTh S l e + leOe (ugTh S l f) * gxTh (upsilon l) (ldAtR S l) c' :=
    fun c' hc' hc'1 hc'c => ugAddT hl hX heH hfH ((ldHull_iff hl hX (hc'c.trans_lt hcW)).2 hc') hc'1
      (hc'c.trans_lt hcW) hd ((add_le_add_iff_left e).2 (mul_le_mul_right hc'c _) |>.trans_lt hlt)
  have hOf0 : leOe (ugTh S l f) ≠ 0 := (leOe_pos _).ne'
  refine ⟨fun m => ∃ c', GxCl (upsilon l) (ldAtR S l) c' ∧ 1 ≤ c' ∧ c' < c ∧ m = e + leWe f * c', ?_,
    ⟨_, 1, hc1, le_rfl, h1c, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨c', hc', hc'1, hc'c, rfl⟩
    exact ⟨CSet.add_mem heH (leMulWe_mem hfH ((ldHull_iff hl hX (hc'c.trans hcW)).2 hc')),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc'1))).trans le_add_self,
      hmlt c' hc'c⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvc : v < leWe f * c := (add_lt_add_iff_left e).1 hy
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    set c1 := v / leWe f with hc1_def
    have hc1c : c1 < c := (Ordinal.lt_mul_iff_div_lt (leWe_pos f).ne').1 hvc
    have hvW : v < ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by
      have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
      rw [← this, leWe_succ]; exact hvc.trans_le (mul_le_mul_right hcW.le _)
    have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hvH hvW
    have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX (hc1c.trans hcW)).1 hc1H
    have hcs : c1 + 1 < c := hlim.add_one_lt hc1c
    refine ⟨_, ⟨c1 + 1, rqCode_succ hl hX hc1c' (hcs.trans hcW), le_add_self, hcs, rfl⟩, ?_⟩
    refine (add_lt_add_iff_left e).2 ?_
    have h := Ordinal.lt_mul_succ_div v (leWe_pos f).ne'
    rwa [Order.succ_eq_add_one] at h
  · intro z hz
    rw [hT c hc h1c.le le_rfl] at hz
    rcases lt_or_ge z (ugTh S l e) with hze | hze
    · refine ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, ?_⟩
      rw [hT 1 hc1 le_rfl h1c.le, hΘ1, mul_one]; exact hze.trans_le le_self_add
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwc : w < leOe (ugTh S l f) * gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left _).1 hz
    have hw2 : w / leOe (ugTh S l f) < gxTh (upsilon l) (ldAtR S l) c :=
      (Ordinal.lt_mul_iff_div_lt hOf0).1 hwc
    obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hw2
    have hcs : c0 + 1 < c := hlim.add_one_lt hc0c
    have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
    refine ⟨_, ⟨c0 + 1, hcc, le_add_self, hcs, rfl⟩, ?_⟩
    rw [hT _ hcc le_add_self hcs.le, gxTh_add hρSC hAt hc0, hΘ1, e0]
    refine (add_lt_add_iff_left _).2 ?_
    have h := Ordinal.lt_mul_succ_div w hOf0
    rwa [Order.succ_eq_add_one] at h
  · rintro Q hQ m h ⟨c', hc', hc'1, hc'c, rfl⟩ h1 h2 hh
    exact uqRangeX hQ hd hcW hc'1 h1 h2 hh

/-- **`e + W^{f+1}`** (`W^{f+1} ∣ e`, `< Y₃`): members `e + W^f·c` indexed by the codes `c`. -/
theorem uqMB_succ {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe (f + 1) < ugY S) : UqMB S l (e + leWe (f + 1)) := by
  have hf1H : f + 1 ∈ cdHull S l := CSet.succ_mem hfH
  have hfE : f + 1 < ugY S := (tnLe_We _).trans_lt (le_add_self.trans_lt hlt)
  have hTf1 : ugTh S l (f + 1) = ugTh S l f + 1 := ugSucc hl hX hfH hfE
  have hTE : ugTh S l (e + leWe (f + 1)) = ugTh S l e + leOe (ugTh S l f + 1) := by
    rw [ugAddW hl hX heH hf1H hd hlt, hTf1]
  have hmlt : ∀ c, c < Om (1 + 1) → e + leWe f * c < e + leWe (f + 1) := fun c hc => by
    rw [leWe_succ]; exact (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left hc (leWe_pos f))
  have hTedvd : leOe (ugTh S l f + 1) ∣ ugTh S l e := by
    have h := ugDvd hl hX e heH (le_self_add.trans_lt hlt) (f + 1) hf1H hd
    rwa [hTf1] at h
  refine ⟨fun c => e + leWe f * c, fun c => ugTh S l e + leOe (ugTh S l f) * c,
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _),
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    refine ⟨CSet.add_mem heH (leMulWe_mem hfH hcH),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc1))).trans le_add_self,
      hmlt c hcW, ugAddT hl hX heH hfH hcH hc1 hcW hd ((hmlt c hcW).trans hlt), ?_⟩
    rw [hTE, leOe_succ]
    exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (snTh_lt_Om1 hl hX hcW.le) (leOe_pos _))
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < e + leWe f * 1; rw [mul_one]; exact hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe (f + 1) := (add_lt_add_iff_left e).1 hwE
    have hxc := uqModW hQ hd hx hw
    have hxe : x < leWe f * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := uqCofK (k := 1 + 1) hQ ugTwo_ne hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    rcases lt_or_ge w (ugTh S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, by
        show w < ugTh S l e + leOe (ugTh S l f) * 1; rw [mul_one]; exact hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (ugTh S l f + 1) := (add_lt_add_iff_left _).1 hwE
    have hxc := uqModO hQ hTedvd hx hw
    have hxe : x < leOe (ugTh S l f) * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := uqCofK (k := 1) hQ one_ne_zero hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 hxc'⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have k1 : e + leWe f ≤ h :=
      ((add_le_add_iff_left e).2 ((mul_one (leWe f)).symm.le.trans (mul_le_mul_right hc1 _))).trans h1
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := uqHeadE hQ hd k1 h2 hh
    exact UgC.add heQ (uqMulW hQ (uqCl_of_succ hQ hh'1 hh'2 hh'c) (UgC.small hcQ))

/-- **`e + W^f` from the countable members of `f`** (`W^f ∣ e`, `< Y₃`): members `e + W^m`. -/
theorem uqMA_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < ugY S) (hA : UqMA S l f) : UqMA S l (e + leWe f) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  have hTm : ∀ m, Mem m → ugTh S l (e + leWe m) = ugTh S l e + leOe (ugTh S l m) := fun m hm =>
    ugAddW hl hX heH (hdat m hm).1 ((leWe_dvd (hdat m hm).2.2.le).trans hd)
      (((add_le_add_iff_left e).2 (leWe_mono (hdat m hm).2.2.le)).trans_lt hlt)
  have hTE := ugAddW hl hX heH hfH hd hlt
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = e + leWe m, ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    obtain ⟨hmH, -, hmf⟩ := hdat m hm
    exact ⟨CSet.add_mem heH (leWe_mem hmH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hmf)⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvf : v < leWe f := (add_lt_add_iff_left e).1 hy
    rcases eq_or_ne v 0 with rfl | hv0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos _)⟩
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    have htH : sgLW v ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hvH)
    obtain ⟨m, hm, htm⟩ := hA1 _ htH (tuLogW_lt hv0 hvf)
    exact ⟨_, ⟨m, hm, rfl⟩, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt v) (Order.add_one_le_of_lt htm))⟩
  · intro z hz
    rw [hTE] at hz
    have hany : ∀ m, Mem m → ugTh S l e < ugTh S l (e + leWe m) := fun m hm => by
      rw [hTm m hm]; exact lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge z (ugTh S l e) with hze | hze
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hze.trans (hany m0 hm0)⟩
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwf : w < leOe (ugTh S l f) := (add_lt_add_iff_left _).1 hz
    rcases eq_or_ne w 0 with rfl | hw0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact hany m0 hm0⟩
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hw0 hwf)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    exact (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log w) (Order.add_one_le_of_lt hum))
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := uqHeadE hQ hd h1 h2 hh
    exact UgC.add heQ (uqWe hQ (hA3 Q hQ m h' hm hh'1 hh'2 hh'c))

/-- **`e + W^f` from the members of `f` indexed by the codes** (`W^f ∣ e`, `< Y₃`): members `e + W^{M c}`. -/
theorem uqMB_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < ugY S) (hB : UqMB S l f) : UqMB S l (e + leWe f) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have hTE := ugAddW hl hX heH hfH hd hlt
  have hTedvd : leOe (ugTh S l f) ∣ ugTh S l e :=
    ugDvd hl hX e heH (le_self_add.trans_lt hlt) f hfH hd
  refine ⟨fun c => e + leWe (M c), fun c => ugTh S l e + leOe (Mh c),
    fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)),
    fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, -, hMf, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    refine ⟨CSet.add_mem heH (leWe_mem hMH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hMf), ?_, ?_⟩
    · rw [ugAddW hl hX heH hMH ((leWe_dvd hMf.le).trans hd)
        (((add_le_add_iff_left e).2 (leWe_mono hMf.le)).trans_lt hlt), hTM]
    · rw [hTE]; exact (add_lt_add_iff_left _).2 (leOe_lt hMhT)
  · intro Q hQ hQ1 w hw hwE
    have hM1lt : e < e + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe f := (add_lt_add_iff_left e).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := uqModW hQ hd hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (ugC_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    have hM1lt : ugTh S l e < ugTh S l e + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w (ugTh S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (ugTh S l f) := (add_lt_add_iff_left _).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := uqModO hQ hTedvd hx hw
    have huc : UgC S 1 Q (log ω x / Om 1) := ugC_div hQ one_ne_zero _ (ugCDec hQ one_ne_zero x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := uqHeadE hQ hd h1 h2 hh
    exact UgC.add heQ (uqWe hQ (hB3 Q hQ c h' hc1' hcQ hh'1 hh'2 hh'c))

/-- **EVERY LIMIT EXPONENT `e + r < B` OF `H_λ` (`W^{log_W r + 1} ∣ e`, `B ≤ Y₃`) HAS A MEMBER SYSTEM**, given the
member systems at the `W`-fixed limits `Γ₂ ≤ r < B` (`UqFixMS S λ B`). -/
theorem uqMS {B : Ordinal.{0}} (hF : UqFixMS S l B) (hB : B ≤ ugY S) : ∀ r, r ∈ cdHull S l → IsSuccLimit r →
    ∀ e, e ∈ cdHull S l → e + r < B → leWe (sgLW r + 1) ∣ e → UqMA S l (e + r) ∨ UqMB S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hrlim e heH hltB hd
  have hlt : e + r < ugY S := hltB.trans_le hB
  have hrB : r < B := le_add_self.trans_lt hltB
  have hrY : r < ugY S := le_add_self.trans_lt hlt
  have hr0 : 0 < r := hrlim.bot_lt
  by_cases hrs : sgLW r < r
  swap
  · have hWr : leWe r = r := uaW_fix hr0 hrs
    have hsr : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hrs)
    have hdr : leWe r ∣ e := (leWe_dvd (le_self_add : r ≤ r + 1)).trans (by rw [← hsr]; exact hd)
    have hlt' : e + leWe r < ugY S := by rw [hWr]; exact hlt
    have hMS : UqMA S l r ∨ UqMB S l r := by
      rcases lt_or_ge r uaGam with hrG | hrG
      · have h := Ud.udMS hl hX r hrH hrlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
        rw [zero_add] at h
        rcases h with hA | hB
        · exact Or.inl (uqMA_of_ua hrG hA)
        · exact Or.inr (uqMB_of_ua hl hX hrH hrG hB)
      refine hF r hrH hrG hrB hrs fun r' hr'H hr'lim hr'r => ?_
      have h := IH r' hr'r hr'H hr'lim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hr'r.trans hrB)
        (dvd_zero _)
      rwa [zero_add] at h
    rw [← hWr]
    rcases hMS with hA | hB
    · exact Or.inl (uqMA_lift hl hX heH hrH hdr hlt' hA)
    · exact Or.inr (uqMB_lift hl hX heH hrH hdr hlt' hB)
  obtain ⟨hfH, -, hcc, hc1, hcW, hr'H, hr'f, hrdec⟩ := uaBase hl hX hrH hr0
  have hfr : sgLW r < r := hrs
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
      have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
      have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
      have he2r : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
      have hd2 : leWe f ∣ e + leWe f * c1 := dvd_add hdf (dvd_mul_right _ _)
      have hlt2 : e + leWe f * c1 + leWe f < ugY S := he2r ▸ hlt
      rw [← he2r]
      rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f1, hfs⟩ | hflim
      · exfalso
        have hrc1 : r = c1 + 1 := by rw [hrc, hf0, leWe_zero, one_mul, ← hcs]
        have h := hrlim.succ_lt (show c1 < r from hrc1 ▸ lt_add_one c1)
        rw [Order.succ_eq_add_one, ← hrc1] at h
        exact lt_irrefl _ h
      · rw [succ_eq_add_one] at hfs
        have hf1H : f1 ∈ cdHull S l := mem_of_add_one_mem (hfs ▸ hfH)
        rw [← hfs] at hd2 hlt2 he2H ⊢
        exact Or.inr (uqMB_succ hl hX he2H hf1H hd2 hlt2)
      · have hMSf := IH f hfr hfH hflim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hfr.trans hrB)
          (dvd_zero _)
        rw [zero_add] at hMSf
        rcases hMSf with hA | hB
        · exact Or.inl (uqMA_lift hl hX he2H hfH hd2 hlt2 hA)
        · exact Or.inr (uqMB_lift hl hX he2H hfH hd2 hlt2 hB)
    · rw [hrc] at hlt ⊢
      exact Or.inl (uqMA_coef hl hX heH hfH hcc hclim hcW hd hlt)
  · have hr'lim : IsSuccLimit r' := by
      rcases zero_or_succ_or_isSuccLimit r' with h0 | ⟨r1, hr1⟩ | hl'
      · exact absurd h0 hr'0
      · exfalso
        rw [succ_eq_add_one] at hr1
        have hr2 : r = leWe f * c + r1 + 1 := by rw [add_assoc, hr1]; exact hrdec
        have h := hrlim.succ_lt (show leWe f * c + r1 < r from hr2 ▸ lt_add_one _)
        rw [Order.succ_eq_add_one, ← hr2] at h
        exact lt_irrefl _ h
      · exact hl'
    have hs' : sgLW r' < f := tuLogW_lt hr'0 hr'f
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have h := IH r' hr'r hr'H hr'lim (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hltB) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
    rwa [he2] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
