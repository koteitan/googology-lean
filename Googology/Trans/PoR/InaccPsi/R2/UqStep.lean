import Googology.Trans.PoR.InaccPsi.R2.UqHd

/-!
# The step and the ladder past `Γ₂` with the bound `Y₃` and the image `T = Ug.ugTh`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `C_k(Q) = Ug.UgC S k Q`, `CL₃ = Ug.UgCL`,
`Y₃ = ψ_{Ω₃}(Ω₃)`; prefixes past `Γ₂` `Uq.UqPD`.

**A weak prefix** `UqPDw S λ P P̂`: a prefix `Uq.UqPD`, or `P = P̂ = 0`.  **The step at `e`** `UqStepX S λ e`: a weak
prefix `(P, P̂)` with `W^e ∣ P`, `Ω^{T e} ∣ P̂`, `P + W^e < Y₃` gives the prefix `P + W^e` with the image
`P̂ + Ω^{T e}`; **the ladder at `e`** `UqLadX S λ e`: the prefixes `P + W^e·c` (images `P̂ + Ω^{T e}·Θ c`) for every
code `1 ≤ c < Ω₂` (`W^{e+1} ∣ P`, `Ω^{T e + 1} ∣ P̂`, `P + W^{e+1} < Y₃`).  **Member systems** `UqMA`, `UqMB`:
`Ua.UaMA`, `Ua.UaMB` with the image `T` and the level-2 codes.  No exponent is bounded by `Γ₂`.

* `UqPDw`, `uqPDw_data`, `UqStepX`, `UqLadX`, `uqImg_step`, `uqImg_lad`, `uqLadDown`;
* `uqLad_of_step` (**the step at `e` gives the ladder at `e`**), `uqStep_succ` (**the ladder at `e` gives the step at
  `e + 1`**, by `Uq.uqLevLimM`), `uqStepOne` (**the step at `1`**);
* `UqMA`, `UqMB`, `uqStep_MA`, `uqStep_MB` (**a member system and the steps of the members give the step**).

No new axiom.  New definitions: `UqPDw`, `UqStepX`, `UqLadX`, `UqMA`, `UqMB`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Tu
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Um

variable {S : InaccSeq.{0}}

/-- **A weak prefix past `Γ₂` with the bound `Y₃`**: a prefix `UqPD`, or `P = P̂ = 0`. -/
def UqPDw (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop := UqPD S l P Ph ∨ (P = 0 ∧ Ph = 0)

/-- The data of a weak prefix. -/
theorem uqPDw_data {l P Ph : Ordinal.{0}} (h : UqPDw S l P Ph) :
    Om (1 + 1) ∣ P ∧ P ∈ cdHull S l ∧ UqImg S l P Ph := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact ⟨h.dvd, h.hull, h.img⟩
  · exact ⟨dvd_zero _, CSet.zero_mem _ _, fun _ _ _ Q hQ _ => UgC.zero hQ.1⟩

/-- **The step at the exponent `e`** with the image `T e`, from every weak prefix. -/
def UqStepX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, UqPDw S l P Ph → leWe e ∣ P → leOe (ugTh S l e) ∣ Ph → P + leWe e < ugY S →
    UqPD S l (P + leWe e) (Ph + leOe (ugTh S l e))

/-- **The ladder at the exponent `e`**, from every weak prefix. -/
def UqLadX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, UqPDw S l P Ph → leWe (e + 1) ∣ P → leOe (ugTh S l e + 1) ∣ Ph → P + leWe (e + 1) < ugY S →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      UqPD S l (P + leWe e * c) (Ph + leOe (ugTh S l e) * gxTh (upsilon l) (ldAtR S l) c)

/-- **Members of `E`** (countable family; image `T`, level-2 codes). -/
def UqMA (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∃ Mem : Ordinal.{0} → Prop, (∀ m, Mem m → m ∈ cdHull S l ∧ 1 ≤ m ∧ m < E) ∧ (∃ m, Mem m) ∧
    (∀ y, y ∈ cdHull S l → y < E → ∃ m, Mem m ∧ y < m) ∧
    (∀ z, z < ugTh S l E → ∃ m, Mem m ∧ z < ugTh S l m) ∧
    (∀ Q, SC Q → ∀ m h, Mem m → m ≤ h → h ≤ E → UgC S (1 + 1) Q h → UgC S (1 + 1) Q m)

/-- **Members of `E` indexed by the codes** (image `T`, level-2 codes). -/
def UqMB (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Prop :=
  ∃ M Mh : Ordinal.{0} → Ordinal.{0}, Monotone M ∧ Monotone Mh ∧
    (∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      M c ∈ cdHull S l ∧ 1 ≤ M c ∧ M c < E ∧ ugTh S l (M c) = Mh (gxTh (upsilon l) (ldAtR S l) c) ∧
        Mh (gxTh (upsilon l) (ldAtR S l) c) < ugTh S l E) ∧
    (∀ Q, SC Q → Om 1 < Q → ∀ w, UgC S (1 + 1) Q w → w < E → ∃ c', c' < Q ∧ w < M c') ∧
    (∀ Q, SC Q → ∀ w, UgC S 1 Q w → w < ugTh S l E → ∃ c', c' < Q ∧ w < Mh c') ∧
    (∀ Q, SC Q → ∀ c h, 1 ≤ c → c < Q → M c ≤ h → h ≤ E → UgC S (1 + 1) Q h → UgC S (1 + 1) Q (M c))

/-- **At a base past `Γ₂`, `CL₃ (P + W^e·c)` gives `CL₃ (P + W^e·c')` for every `1 ≤ c' ≤ c`.** -/
theorem uqLadDown {l β X0 Xh0 P e c c' : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + leWe e * c) < ugY S)
    (hb : RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β) (hd : leWe (e + 1) ∣ P)
    (hcW : c < Om (1 + 1)) (hcl : UgCL S (P + leWe e * c) β X0) (hc1 : 1 ≤ c') (hc' : c' ≤ c) :
    UgCL S (P + leWe e * c') β X0 := by
  have hy : P + leWe e * c' ≤ P + leWe e * c := (add_le_add_iff_left P).2 (mul_le_mul_right hc' _)
  obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff hG3 hb hcl hy
  intro Q hQ hQ'
  have hzc := hz Q hQ hQ'
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hx1 : leWe e * c' ≤ x := (add_le_add_iff_left P).1 hz1
  have hx2 : x ≤ leWe e * c := (add_le_add_iff_left P).1 hz2
  set c'' := x / leWe e with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.mul_le_iff_le_div (leWe_pos e).ne').1 hx1
  have hc''W : c'' < Om (1 + 1) := hc''c.trans_lt hcW
  have ex : P + x = P + leWe e * c'' + x % leWe e := by rw [add_assoc, Ordinal.div_add_mod]
  rw [ex] at hzc
  have hP' : UgC S (1 + 1) Q (P + leWe e * c'') := by
    rcases eq_or_ne (x % leWe e) 0 with h0 | h0
    · rwa [h0, add_zero] at hzc
    have hdv : leWe e ∣ P + leWe e * c'' := dvd_add hdE (dvd_mul_right _ _)
    have h1 : P + leWe e * c'' + leWe 0 ≤ P + leWe e * c'' + x % leWe e := by
      rw [leWe_zero]; exact (add_le_add_iff_left _).2 (Order.one_le_iff_ne_zero.2 h0)
    have h2 : P + leWe e * c'' + x % leWe e ≤ P + leWe e * c'' + leWe e :=
      (add_le_add_iff_left _).2 (Ordinal.mod_lt _ (leWe_pos e).ne').le
    exact (uqHeadE hQ hdv h1 h2 hzc).1
  obtain ⟨hP, hec, hc''Q⟩ := uqCodeHeadX hQ hd (hc1.trans hc'c'') hc''W hP'
  exact UgC.add hP (uqMulW hQ hec (UgC.small (hc'c''.trans_lt hc''Q)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The image condition of `P + W^e` with the image `P̂ + Ω^{T e}`. -/
theorem uqImg_step {P Ph e : Ordinal.{0}} (himg : UqImg S l P Ph) (hd : leWe e ∣ P) (heH : e ∈ cdHull S l)
    (heY : e < ugY S) : UqImg S l (P + leWe e) (Ph + leOe (ugTh S l e)) := by
  intro T hT hcl Q hQ hΘQ
  have hPc : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q P := fun Q hQ hTQ =>
    (uqHeadE hQ hd le_rfl le_rfl (hcl Q hQ hTQ)).1
  have heQ : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q e := fun Q hQ hTQ => by
    obtain ⟨-, h, h1, h2, hh⟩ := uqHeadE hQ hd le_rfl le_rfl (hcl Q hQ hTQ)
    rwa [le_antisymm h2 h1] at hh
  exact UgC.add (himg T hT hPc Q hQ hΘQ) (uqOe hQ (ugOwn hl hX e heH heY T hT heQ Q hQ hΘQ))

/-- The image condition of `P + W^e·c` with the image `P̂ + Ω^{T e}·Θ c`. -/
theorem uqImg_lad {P Ph e c : Ordinal.{0}} (himg : UqImg S l P Ph) (hd : leWe (e + 1) ∣ P)
    (heH : e ∈ cdHull S l) (heY : e < ugY S) (hc : GxCl (upsilon l) (ldAtR S l) c) (hc1 : 1 ≤ c)
    (hcW : c < Om (1 + 1)) :
    UqImg S l (P + leWe e * c) (Ph + leOe (ugTh S l e) * gxTh (upsilon l) (ldAtR S l) c) := by
  intro T hT hcl Q hQ hΘQ
  have hPc : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q P := fun Q hQ hTQ =>
    (uqCodeHeadX hQ hd hc1 hcW (hcl Q hQ hTQ)).1
  have heQ : ∀ Q, SC Q → T ≤ Q → UgC S (1 + 1) Q e := fun Q hQ hTQ =>
    (uqCodeHeadX hQ hd hc1 hcW (hcl Q hQ hTQ)).2.1
  have hcT : c < T := (uqCodeHeadX hT hd hc1 hcW (hcl T hT le_rfl)).2.2
  have hΘ := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
  exact UgC.add (himg T hT hPc Q hQ hΘQ)
    (uqMulO hQ (ugOwn hl hX e heH heY T hT heQ Q hQ hΘQ) (UgC.small (hΘ.trans_le hΘQ)))

/-- **The step at `e` gives the ladder at `e`** (`1 ≤ e < Y₃` in `H_λ`). -/
theorem uqLad_of_step {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heY : e < ugY S)
    (hS : UqStepX S l e) : UqLadX S l e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  set Te := ugTh S l e with hTe
  intro P Ph hD hd hdh hPY c
  obtain ⟨hPdv, hPH, hPimg⟩ := uqPDw_data hD
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  have hdhE : leOe Te ∣ Ph := (tuOe_dvd (le_self_add : Te ≤ Te + 1)).trans hdh
  have hOe0 : leOe Te ≠ 0 := (leOe_pos _).ne'
  have hWe : Om (1 + 1) ∣ leWe e := by rw [← leWe_one]; exact leWe_dvd he1
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc1' hcW
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  have hEY : P + leWe e * c < ugY S := by
    refine lt_of_le_of_lt ?_ hPY
    rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_right hcW.le _)
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c0, hc0⟩ | hlim
  · rw [h0] at hc1'; exact absurd hc1' (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hc0
    subst hc0
    have hc0c : GxCl (upsilon l) (ldAtR S l) c0 := rqCode_pred hl hX hc hcW
    have hc0W : c0 < Om (1 + 1) := (lt_add_one c0).trans hcW
    have e1 : P + leWe e * (c0 + 1) = P + leWe e * c0 + leWe e := by rw [mul_add_one, add_assoc]
    have e2 : Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) (c0 + 1) =
        Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c0 + leOe Te := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one, add_assoc]
    rcases eq_or_ne c0 0 with rfl | hc00
    · rw [zero_add, mul_one, hΘ1, mul_one]
      rw [zero_add, mul_one] at hEY
      exact hS P Ph hD hdE hdhE hEY
    have IH0 := IH c0 (lt_add_one c0) hc0c (Order.one_le_iff_ne_zero.2 hc00) hc0W
    rw [e1] at hEY
    have h := hS _ _ (Or.inl IH0) (dvd_add hdE (dvd_mul_right _ _)) (dvd_add hdhE (dvd_mul_right _ _)) hEY
    rw [e1, e2]; exact h
  · have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hDdv : Om (1 + 1) ∣ P + leWe e * c := dvd_add hPdv (hWe.trans (dvd_mul_right _ _))
    have hH : P + leWe e * c ∈ cdHull S l := CSet.add_mem hPH (leMulWe_mem heH hcH)
    have hE1 : 1 ≤ P + leWe e * c :=
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos e) (zero_lt_one.trans_le hc1'))).trans le_add_self
    have himg := uqImg_lad hl hX hPimg hd heH heY hc hc1' hcW
    have hP := uqOwP_img hl hX himg hH hE1
    refine ⟨hDdv, hH, hE1, hEY, himg, ?_⟩
    have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 →
        X0 + leWe (P + leWe e * c) < ugY S →
        RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β → UgCL S (P + leWe e * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
        ∃ e' eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e' eh ∧ UjLev S l Owe e' eh ∧
          Owe β X0 ∧ e' < P + leWe e * c ∧ eh < Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c ∧
          e' = P + leWe e * c' ∧ eh = Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
      have hD' := IH c' hc'c hc' hc'1 (hc'c.trans hcW)
      exact ⟨_, _, UgCL S (P + leWe e * c'), uqOwP_img hl hX hD'.img hD'.hull hD'.one, hD'.lev,
        uqLadDown hoff hG3 hb hd hcW hcl hc'1 hc'c.le,
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left hc'c (leWe_pos e)),
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c) (leOe_pos _)), rfl, rfl⟩
    refine umLevLimB hl hX hP ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases lt_or_ge y (leWe P) with hyP | hyP
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
      obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
      set Y := log ω y / Om (1 + 1) with hY_def
      have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
      obtain ⟨x, hx⟩ := exists_add_of_le hY1
      have hxc : x < leWe e * c := (add_lt_add_iff_left P).1 (hx ▸ hY2)
      have hxH : x ∈ cdHull S l := by
        have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
      set c1 := x / leWe e with hc1_def
      have hc1c : c1 < c := (Ordinal.lt_mul_iff_div_lt (leWe_pos e).ne').1 hxc
      have hc1W : c1 < Om (1 + 1) := hc1c.trans hcW
      have hxW : x < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
        have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this, leWe_succ]; exact hxc.trans_le (mul_le_mul_right hcW.le _)
      have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hxH hxW
      have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX hc1W).1 hc1H
      have hcs : c1 + 1 < c := hlim.succ_lt hc1c
      have hcc := rqCode_succ hl hX hc1c' (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
      rw [← hY_def, hx]
      refine (add_assoc P x 1).le.trans ((add_le_add_iff_left P).2 (Order.add_one_le_of_lt ?_))
      have h := Ordinal.lt_mul_succ_div x (leWe_pos e).ne'
      rwa [Order.succ_eq_add_one] at h
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
      rcases eq_or_ne z 0 with rfl | hz0
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨e', eh, Owe, a1, a2, a3, a4, a5, leOe_pos _⟩
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hq : log ω z / Om 1 < Ph + leOe Te * Θc :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      obtain ⟨v, hv⟩ := exists_add_of_le hqP
      have hvc : v < leOe Te * Θc := (add_lt_add_iff_left _).1 (hv ▸ hq)
      have hv2 : v / leOe Te < Θc := (Ordinal.lt_mul_iff_div_lt hOe0).1 hvc
      obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hv2
      have hcs : c0 + 1 < c := hlim.succ_lt hc0c
      have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
      rw [hv]
      refine (add_assoc Ph v 1).le.trans ((add_le_add_iff_left Ph).2 (Order.add_one_le_of_lt ?_))
      rw [gxTh_add hρSC hAt hc0, hΘ1, e0]
      have h := Ordinal.lt_mul_succ_div v hOe0
      rwa [Order.succ_eq_add_one] at h

/-- **The ladder at `e` gives the step at `e + 1`** (`e + 1 < Y₃`), from every weak prefix. -/
theorem uqStep_succ {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (heY : e + 1 < ugY S) (hL : UqLadX S l e) :
    UqStepX S l (e + 1) := by
  have he'H : e + 1 ∈ cdHull S l := CSet.succ_mem heH
  have hT1 : ugTh S l (e + 1) = ugTh S l e + 1 := ugSucc hl hX heH heY
  set Te := ugTh S l e with hTe
  intro P Ph hD hd hdh hPY
  obtain ⟨hPdv, hPH, hPimg⟩ := uqPDw_data hD
  rw [hT1] at hdh ⊢
  have himg : UqImg S l (P + leWe (e + 1)) (Ph + leOe (Te + 1)) := by
    have h := uqImg_step hl hX hPimg hd he'H heY
    rwa [hT1] at h
  have hH : P + leWe (e + 1) ∈ cdHull S l := CSet.add_mem hPH (leWe_mem he'H)
  have h1 : 1 ≤ P + leWe (e + 1) := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hWd : Om (1 + 1) ∣ leWe (e + 1) := by rw [← leWe_one]; exact leWe_dvd le_add_self
  refine ⟨dvd_add hPdv hWd, hH, h1, hPY, himg, ?_⟩
  refine uqLevLimM hl hX (M := fun d => P + leWe e * d) (Mh := fun d => Ph + leOe Te * d)
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _))
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _))
    (uqOwP_img hl hX himg hH h1) hPY ?_ ?_ ?_ ?_
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < P + leWe e * 1; rw [mul_one]; exact hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe (e + 1) := (add_lt_add_iff_left P).1 hwE
    have hxc : UgC S (1 + 1) Q x := uqModW hQ hd hx hw
    have hxe : x < leWe e * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := uqCofK (k := 1 + 1) hQ ugTwo_ne hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left P).2 hxc'⟩
  · intro Q hQ w hw hwE
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < Ph + leOe Te * 1; rw [mul_one]; exact hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (Te + 1) := (add_lt_add_iff_left Ph).1 hwE
    have hxc : UgC S 1 Q x := uqModO hQ hdh hx hw
    have hxe : x < leOe Te * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := uqCofK (k := 1) hQ one_ne_zero hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 hxc'⟩
  · intro c hc hc1 hcW
    have hDc := hL P Ph hD hd hdh hPY c hc hc1 hcW
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    refine ⟨uqOwP_img hl hX hDc.img hDc.hull hDc.one, hDc.lev, ?_, ?_⟩
    · show P + leWe e * c < P + leWe (e + 1)
      rw [leWe_succ]; exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left hcW (leWe_pos e))
    · show Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c < Ph + leOe (Te + 1)
      rw [leOe_succ]; exact (add_lt_add_iff_left Ph).2 (mul_lt_mul_of_pos_left hΘcO (leOe_pos _))
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    have hy : P + leWe e * c ≤ P + leWe (e + 1) := by
      rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_right hcW.le _)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    have h1z : P + leWe e ≤ z :=
      ((add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_right hc1 _))).trans hz1
    obtain ⟨hP, h, hh1, hh2, hhc⟩ := uqHeadE hQ hd h1z hz2 (hz Q hQ hQ')
    exact UgC.add hP (uqMulW hQ (uqCl_of_succ hQ hh1 hh2 hhc) (UgC.small (hcT.trans_le hQ')))

/-- **The step at `e = 1`**: `P + Ω₂` with the image `P̂ + Ω₁` from every weak prefix. -/
theorem uqStepOne : UqStepX S l 1 := by
  have h1G : (1 : Ordinal.{0}) < uaGam := (gg_one_lt_of_SC ldOm2_SC).trans uaGam_spec.2
  have hT1 : ugTh S l 1 = 1 := by
    rw [ugTh_lt h1G, uaThCode hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX]
  intro P Ph hD _ hdh hPY
  rw [hT1, leWe_one, leOe_one] at *
  rcases hD with hD | ⟨rfl, rfl⟩
  · exact uqPreW hl hX hD hdh
  · rw [zero_add, zero_add]
    refine ⟨dvd_rfl, mxOm2_mem _ _, (gg_one_lt_of_SC ldOm2_SC).le, uqW_lt_Y,
      fun _ _ _ _ _ _ => UgC.om, ?_⟩
    exact umLevUp (umLev_W hl hX) (fun _ _ _ h hb => ugCL_mono h hb le_rfl) (fun _ _ _ _ _ _ _ _ => trivial)

/-- **Countable members give the step** (weak prefixes, image `T`, bound `Y₃`). -/
theorem uqStep_MA {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEY : E < ugY S)
    (hA : UqMA S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → UqStepX S l m) : UqStepX S l E := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  intro P Ph hD hdP hdh hPY
  obtain ⟨hPdv, hPH, hPimg⟩ := uqPDw_data hD
  have himg := uqImg_step hl hX hPimg hdP hEH hEY
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hPH (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hWd : Om (1 + 1) ∣ leWe E := by rw [← leWe_one]; exact leWe_dvd hE1
  refine ⟨dvd_add hPdv hWd, hH, h1, hPY, himg, ?_⟩
  have hP := uqOwP_img hl hX himg hH h1
  have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → X0 + leWe (P + leWe E) < ugY S →
      RoBaseE S l (X0 + leWe (P + leWe E)) 0 β → UgCL S (P + leWe E) β X0 → ∀ m, Mem m →
      ∃ g gh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe g gh ∧ UjLev S l Owe g gh ∧
        Owe β X0 ∧ g < P + leWe E ∧ gh < Ph + leOe (ugTh S l E) ∧
        g = P + leWe m ∧ gh = Ph + leOe (ugTh S l m) := by
    intro β X0 Xh0 hoff hG3 hb hcl m hm
    obtain ⟨hmH, hm1, hmE⟩ := hdat m hm
    have hmY : P + leWe m < ugY S := lt_of_le_of_lt ((add_le_add_iff_left P).2 (leWe_mono hmE.le)) hPY
    have hD' := IH m hmH hm1 hmE P Ph hD ((leWe_dvd hmE.le).trans hdP)
      ((tuOe_dvd (ugLe hl hX hmH hEH hEY hmE.le)).trans hdh) hmY
    refine ⟨_, _, UgCL S (P + leWe m), uqOwP_img hl hX hD'.img hD'.hull hD'.one, hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt hmE),
      (add_lt_add_iff_left _).2 (leOe_lt (ugLt hl hX hmH hEH hEY hmE)), rfl, rfl⟩
    have hy : P + leWe m ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hmE.le)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff hG3 hb hcl hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := uqHeadE hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact UgC.add hPc (uqWe hQ (hA3 Q hQ m h hm hh1 hh2 hhc))
  refine umLevLimB hl hX hP ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, hg0, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, by rw [hg0]; exact hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxE : x < leWe E := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    have hyY : y < leWe (P + x + 1) := by rw [← hx]; exact roLt_We_log y
    rcases eq_or_ne x 0 with rfl | hx0
    · have hle : P + 0 + 1 ≤ P + leWe m0 := by
        rw [add_zero]; exact (add_le_add_iff_left P).2 (Order.one_le_iff_pos.2 (leWe_pos _))
      refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, ?_⟩
      rw [hg0]; exact tuWe_step hyY hle
    have huH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    obtain ⟨m, hm, hum⟩ := hA1 _ huH (tuLogW_lt hx0 hxE)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, hg, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, ?_⟩
    rw [hg]
    exact tuWe_step hyY (tuAdd_step (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt hum)))
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, -, hgh0⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hq : log ω z / Om 1 < Ph + leOe (ugTh S l E) := tuLogO_lt hz0 hz
    have hzq := roLt_Oe_log z
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    rw [hv] at hzq hq
    have hvT : v < leOe (ugTh S l E) := (add_lt_add_iff_left _).1 hq
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0, add_zero]; exact (add_le_add_iff_left Ph).2 (Order.one_le_iff_pos.2 (leOe_pos _))
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hv0 hvT)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, hgh⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, tuOe_step hzq ?_⟩
    rw [hgh]
    exact tuAdd_step (tuOe_step (roLt_Oe_log v) (Order.add_one_le_of_lt hum))

/-- **Members indexed by the codes give the step** (weak prefixes, image `T`, bound `Y₃`). -/
theorem uqStep_MB {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEY : E < ugY S)
    (hB : UqMB S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → UqStepX S l m) : UqStepX S l E := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  intro P Ph hD hdP hdh hPY
  obtain ⟨hPdv, hPH, hPimg⟩ := uqPDw_data hD
  have himg := uqImg_step hl hX hPimg hdP hEH hEY
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hPH (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hWd : Om (1 + 1) ∣ leWe E := by rw [← leWe_one]; exact leWe_dvd hE1
  refine ⟨dvd_add hPdv hWd, hH, h1, hPY, himg, ?_⟩
  refine uqLevLimM hl hX (M := fun c => P + leWe (M c)) (Mh := fun c => Ph + leOe (Mh c))
    (fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)))
    (fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)))
    (uqOwP_img hl hX himg hH h1) hPY ?_ ?_ ?_ ?_
  · intro Q hQ hQ1 w hw hwE
    have hM1 : P < P + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe E := (add_lt_add_iff_left P).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := uqModW hQ hdP hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (ugC_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left P).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    have hM1 : Ph < Ph + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (ugTh S l E) := (add_lt_add_iff_left Ph).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := uqModO hQ hdh hx hw
    have huc : UgC S 1 Q (log ω x / Om 1) := ugC_div hQ one_ne_zero _ (ugCDec hQ one_ne_zero x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, hM1', hME, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hmY : P + leWe (M c) < ugY S := lt_of_le_of_lt ((add_le_add_iff_left P).2 (leWe_mono hME.le)) hPY
    have hDc := IH (M c) hMH hM1' hME P Ph hD ((leWe_dvd hME.le).trans hdP)
      ((tuOe_dvd (ugLe hl hX hMH hEH hEY hME.le)).trans hdh) hmY
    rw [hTM] at hDc
    exact ⟨uqOwP_img hl hX hDc.img hDc.hull hDc.one, hDc.lev, (add_lt_add_iff_left P).2 (leWe_lt hME),
      (add_lt_add_iff_left Ph).2 (leOe_lt hMhT)⟩
  · intro β X0 Xh0 hoff _ hG3 hb hOw c hc hc1 hcW hcT
    obtain ⟨-, -, hME, -, -⟩ := hB0 c hc hc1 hcW
    have hy : P + leWe (M c) ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hME.le)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := uqHeadE hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact UgC.add hPc (uqWe hQ (hB3 Q hQ c h hc1 (hcT.trans_le hQ') hh1 hh2 hhc))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
