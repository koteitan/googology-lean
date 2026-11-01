import Googology.Trans.PoR.InaccPsi.R2.XmPlat

/-!
# THE SUCCESSOR STEP of the replacement law `Xi.XiTopUp`: exponent `e` ⇒ exponent `e + 1`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `X = Ω_{k+3}`, `w = W^{X+e}`,
`M = Ω^{T(X+e)} = ω^m`, `m = Ω₁·T(X+e)`.

The top atom of exponent `e + 1` over `β` is `s = ψ₂(β + w·Ω₂)`.  The sub-bases `β_n = β + w·u_n` with
`u_0 = 0`, `u_{n+1} = ψ₂(β_n + w)` (`xmU`) are bases of exponent `e` (`xmBase`), and the law at `e` gives
`Θ(u_{n+1}) = ψ₁(A + 1 + ψ₂(T β + M·(Θ(u_n) + 1)))`.  The plateau lemma (`Xm.xmPlat`, with `B = A + 1`,
`b = T β`, start `x_0 = Θ(u_1)`) gives `ψ₁(A + 1 + ψ₂(T β + M·Ω₁)) ≤ sup_n Θ(u_n) ≤ Θ(s)`, and
`T(β + W^{X+e+1}) = T β + M·Ω₁`; the upper half is `Xd.xdUp_at`.

* `xmU_it` (the iterates increase and lie in every closure containing `β` and `X + e`),
* `xmSucc` (**THE SUCCESSOR STEP**: the law at `e` for every base of exponent `e` ⇒ the law at `e + 1`).

No new axiom.  New definition: `xmU` (the iterates; auxiliary, no repo statement depends on it).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- The iterates `u_0 = 0`, `u_{n+1} = ψ₂(β + w·u_n + w)`. -/
noncomputable def xmU (S : InaccSeq.{0}) (β w : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | n + 1 => S.psi (β + w * xmU S β w n + w) (Om (1 + 1))

theorem xmU_zero (β w : Ordinal.{0}) : xmU S β w 0 = 0 := rfl

theorem xmU_succ (β w : Ordinal.{0}) (n : ℕ) : xmU S β w (n + 1) = S.psi (β + w * xmU S β w n + w) (Om (1 + 1)) :=
  rfl

theorem xmU_lt2 (β w : Ordinal.{0}) (n : ℕ) : xmU S β w n < Om (1 + 1) := by
  cases n with
  | zero => exact Om_pos (add_pos_of_right zero_lt_one 1).ne'
  | succ n => rw [xmU_succ]; exact psi_lt (InR_Om_succ 1) _

/-- **The iterates increase strictly and lie in every closure containing `β` and `g`.** -/
theorem xmU_it {β g : Ordinal.{0}}
    (hown : ∀ d, d ≤ leWe g * Om (1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hgA : ∀ a, β + leWe g ≤ a → g ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    ∀ n : ℕ, xmU S β (leWe g) n < xmU S β (leWe g) (n + 1) ∧
      ∀ a c, β ∈ S.CSet a c → g ∈ S.CSet a c → β + leWe g * xmU S β (leWe g) n ≤ a →
        xmU S β (leWe g) n ∈ S.CSet a c := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set w := leWe g with hwdef
  intro n
  induction n with
  | zero =>
    refine ⟨?_, fun a c _ _ _ => CSet.zero_mem a c⟩
    rw [xmU_succ]; exact (SC_psi hκ2 _).1
  | succ n ih =>
    obtain ⟨hlt, hmem⟩ := ih
    have hS : SC (xmU S β w (n + 1)) := by rw [xmU_succ]; exact SC_psi hκ2 _
    have h1lt : xmU S β w n + 1 < xmU S β w (n + 1) := hS.isSuccLimit.add_one_lt hlt
    have hmem' : ∀ a c, β ∈ S.CSet a c → g ∈ S.CSet a c → β + w * xmU S β w (n + 1) ≤ a →
        xmU S β w (n + 1) ∈ S.CSet a c := by
      intro a c hβ hg ha
      have harg : β + w * xmU S β w n + w < a := by
        rw [add_assoc, ← mul_add_one]
        exact ((add_lt_add_iff_left β).2 (leMulWe_lt h1lt)).trans_le ha
      have hle : β + w * xmU S β w n ≤ a :=
        (add_le_add le_rfl (leMulWe_mono hlt.le)).trans ha
      rw [xmU_succ]
      exact CSet.psi_mem harg hκ2 (mxOm2_mem _ _)
        (CSet.add_mem (CSet.add_mem hβ (leMulWe_mem hg (hmem a c hβ hg hle))) (leWe_mem hg))
    refine ⟨?_, hmem'⟩
    rw [xmU_succ β w (n + 1)]
    set a' := β + w * xmU S β w (n + 1) + w with ha'
    have hd : w * xmU S β w (n + 1) + w ≤ w * Om (1 + 1) := by
      rw [← mul_add_one]; exact leMulWe_mono (Order.add_one_le_of_lt (xmU_lt2 β w (n + 1)))
    have hβa : β ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := by
      have h := hown _ hd; rwa [← add_assoc] at h
    have hga : g ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := hgA a' (by
      rw [ha', add_assoc]; exact add_le_add le_rfl le_add_self)
    exact lt_psi_of_mem hκ2 (hmem' a' _ hβa hga le_self_add) (xmU_lt2 β w (n + 1))

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE SUCCESSOR STEP**: the law at the exponent `e` on every base of exponent `e` gives the law at `e + 1`. -/
theorem xmSucc (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β)
    (IH : ∀ β', VbD S l β' → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β' →
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β') =
        S.psi (A + 1 + S.psi (vbT S l (β' + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + (e + 1)) β) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + (e + 1)))) (Om (1 + 1)))
        (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set w := leWe (X + e) with hwdef
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hw2 : leWe (X + (e + 1)) = w * Om (1 + 1) := by rw [← add_assoc, leWe_succ]
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hB
  rw [hw2] at hβd hβA hβown
  have hexp : e < S.psi (β + w) (Om (1 + 1)) := hexpA e hec le_self_add
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt hκ2 _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (heW.trans ldOm2_lt_OmW)
  have hg1W : X + e + 1 < Om ω := vkOmW.1.isPrincipal hgW (gg_one_lt_of_SC vkOmW.1)
  have hwΩ : w * Om (1 + 1) < Om ω := by rw [← leWe_succ]; exact (leWe_lt_SC vkOmW.1 vkOmW.2 hg1W).1
  have hwW : w < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have hβW : β < Om ω := hβD.2.2
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  have hgH : X + e ∈ cdHull S l := CSet.add_mem (hXmem _ _) heH
  have hgC : X + e ∈ S.CSet (Om ω) (ConjT.th S) := CSet.add_mem (hXmem _ _) (CSet.of_lt heθ)
  have hgD : VbD S l (X + e) := ⟨hgH, hgC, hgW⟩
  have hg1D : VbD S l (X + e + 1) := ⟨CSet.succ_mem hgH, CSet.succ_mem hgC, hg1W⟩
  -- the iterates
  set u := xmU S β w with hudef
  have hgA : ∀ a, β + w ≤ a → X + e ∈ S.CSet a (S.psi a (Om (1 + 1))) := fun a ha =>
    CSet.add_mem (hXmem _ _) (CSet.of_lt (hexp.trans_le (psi_mono hκ2 ha).1))
  have hit := xmU_it (S := S) (β := β) (g := X + e) hβown hgA
  have hu2 : ∀ n, u n < Om (1 + 1) := xmU_lt2 β w
  have hwu : ∀ n, w * u n ≤ w * Om (1 + 1) := fun n => leMulWe_mono (hu2 n).le
  have huA : ∀ n, β + w * u n < ConjT.Aη S (cdEta S l) := fun n =>
    lt_of_le_of_lt (add_le_add le_rfl (hwu n)) hβA
  have hβuW : ∀ n, β + w * u n < Om ω := fun n =>
    vkOmW.1.isPrincipal hβW (lt_of_le_of_lt (hwu n) hwΩ)
  have huH : ∀ n, u n ∈ cdHull S l := fun n => (hit n).2 _ _ hβH hgH (huA n).le
  have huC : ∀ n, u n ∈ S.CSet (Om ω) (ConjT.th S) := fun n => (hit n).2 _ _ hβD.2.1 hgC (hβuW n).le
  have huc : ∀ n, GxCl (upsilon l) (ldAtR S l) (u n) := fun n => (ldHull_iff hl hX (hu2 n)).1 (huH n)
  have hu1W : ∀ n, u n + 1 < Om (1 + 1) := fun n => ldOm2_SC.isSuccLimit.add_one_lt (hu2 n)
  have hwuD : ∀ n, VbD S l (w * (u n + 1) + 0) := fun n => by
    rw [add_zero]
    exact ⟨leMulWe_mem hgH (CSet.succ_mem (huH n)), leMulWe_mem hgC (CSet.succ_mem (huC n)),
      lt_of_le_of_lt (leMulWe_mono (hu1W n).le) hwΩ⟩
  have hβnD : ∀ n, VbD S l (β + w * u n) := fun n =>
    ⟨CSet.add_mem hβH (leMulWe_mem hgH (huH n)), CSet.add_mem hβD.2.1 (leMulWe_mem hgC (huC n)), hβuW n⟩
  have hβnB : ∀ n, Ro.RoBaseE S l X e (β + w * u n) := by
    intro n
    refine ⟨?_, (hβnD n).1, ?_, fun d hd => ?_, fun e'' he'' h'' => ?_⟩
    · exact dvd_add ((dvd_mul_right w (Om (1 + 1))).trans hβd) (dvd_mul_right _ _)
    · rw [add_assoc, ← mul_add_one]
      exact lt_of_le_of_lt (add_le_add le_rfl (leMulWe_mono (Order.add_one_le_of_lt (hu2 n)))) hβA
    · have hd' : w * u n + d ≤ w * Om (1 + 1) := (add_le_add le_rfl hd).trans (by
        rw [← mul_add_one]; exact leMulWe_mono (Order.add_one_le_of_lt (hu2 n)))
      have hβ' := hβown _ hd'
      rw [← add_assoc] at hβ'
      cases n with
      | zero =>
        have hu0 : u 0 = 0 := rfl
        rw [hu0, mul_zero, add_zero] at hβ' ⊢
        exact hβ'
      | succ n =>
        have h1 : 1 ≤ u (n + 1) := Order.one_le_iff_pos.2 ((hit n).1.trans_le' zero_le)
        have hw1 : β + w ≤ β + w * u (n + 1) + d :=
          (add_le_add le_rfl (Ordinal.le_mul_left w (zero_lt_one.trans_le h1))).trans le_self_add
        exact CSet.add_mem hβ' (leMulWe_mem (hgA _ hw1) ((hit (n + 1)).2 _ _ hβ' (hgA _ hw1) le_self_add))
    · refine (hexpA e'' he'' (h''.trans le_self_add)).trans_le (psi_mono hκ2 ?_).1
      exact add_le_add le_self_add le_rfl
  -- `T` at the sub-bases
  have hTβn : ∀ n, vbT S l (β + w * u n + w) =
      vbT S l β + leOe (vbT S l (X + e)) * (gxTh (upsilon l) (ldAtR S l) (u n) + 1) := by
    intro n
    have e1 : β + w * u n + w = β + (w * (u n + 1) + 0) := by rw [add_zero, mul_add_one, add_assoc]
    rw [e1, Vh.vhT_add hl hX hβD (hwuD n), Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.succ_mem (huH n)) (hu1W n),
      Vh.vhT_zero hl hX, add_zero, gxTh_add hρSC hAt (huc n) 1, hΘ1]
  have hΘu : ∀ n, gxTh (upsilon l) (ldAtR S l) (u (n + 1)) =
      S.psi (A + 1 + S.psi (vbT S l β + leOe (vbT S l (X + e)) * (gxTh (upsilon l) (ldAtR S l) (u n) + 1))
        (Om (1 + 1))) (Om 1) := by
    intro n
    have h := IH _ (hβnD n) (hβnB n)
    unfold leTe at h
    rw [hTβn n] at h
    exact h
  -- `T` at the top
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX h1ρ (fun a b => CSet.one_mem a b)
  have hTtop : vbT S l (β + leWe (X + (e + 1))) = vbT S l β + ω ^ (Om 1 * vbT S l (X + e)) * Om 1 := by
    have e1 : leWe (X + (e + 1)) = leWe (X + e + 1) * 1 + 0 := by rw [add_assoc, mul_one, add_zero]
    have hD1 : VbD S l (leWe (X + e + 1) * 1 + 0) := by
      rw [mul_one, add_zero]
      exact ⟨leWe_mem hg1D.1, leWe_mem hg1D.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hg1W).1⟩
    rw [e1, Vh.vhT_add hl hX hβD hD1, Vh.vhT_cnfW hl hX hg1D (Xi.xiD_zero l) (CSet.one_mem _ _)
      (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one, Vh.vhT_add hl hX hgD h1D, hT1,
      leOe_succ]
    rfl
  -- the data of the plateau
  set b := vbT S l β with hbdef
  set m := Om 1 * vbT S l (X + e) with hmdef
  have hMe : leOe (vbT S l (X + e)) = ω ^ m := rfl
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xd.xdTr hl hX hβD hβD hβn
  have hTg : vbT S l (X + e) = Om ((k : Ordinal.{0}) + 1 + 1) + gxTh (upsilon l) (ldAtR S l) e := by
    rw [Vh.vhT_add hl hX (Xi.xiD_Om k l) ⟨heH, CSet.of_lt heθ, heW.trans ldOm2_lt_OmW⟩, vbT_code hl hX heW heH]
    congr 1
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [Xi.xiC2] at h
  have hK2ε : ω ^ Om ((k : Ordinal.{0}) + 1 + 1) = Om ((k : Ordinal.{0}) + 1 + 1) := gg_SC_eps (SC_Om (Xi.xiNe k 1))
  have hOK : Om 1 * Om ((k : Ordinal.{0}) + 1 + 1) = veblen 0 (Om 1 + Om ((k : Ordinal.{0}) + 1 + 1)) := by
    rw [veblen_zero_apply, opow_add, Om1_opow, hK2ε]
  have hmC : ∀ a c, gxTh (upsilon l) (ldAtR S l) e < c → m ∈ S.CSet a c := by
    intro a c hc
    rw [hmdef, hTg, mul_add, hOK]
    exact CSet.add_mem (CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (Sc.scNat_mem a c k)))))) (mem_Om1_mul hc)
  have hu1 : u 1 = S.psi (β + w) (Om (1 + 1)) := by
    show S.psi (β + w * xmU S β w 0 + w) (Om (1 + 1)) = _
    rw [xmU_zero, mul_zero, add_zero]
  set x0 := gxTh (upsilon l) (ldAtR S l) (u 1) with hx0def
  have hex0 : gxTh (upsilon l) (ldAtR S l) e < x0 := gxTh_lt hec (by rw [hu1]; exact hexp)
  have hx0v : x0 = S.psi (A + 1 + S.psi (b + ω ^ m * 1) (Om (1 + 1))) (Om 1) := by
    rw [hx0def, hΘu 0]
    have hu0 : u 0 = 0 := rfl
    rw [hu0, gxTh_zero, zero_add, hMe]
  have hx01 : x0 < Om 1 := by rw [hx0v]; exact psi_lt hκ1 _
  have hx0pos : 1 ≤ x0 := by rw [hx0v]; exact Order.one_le_iff_pos.2 (SC_psi hκ1 _).1
  have h0 : x0 ≤ xmX S (A + 1) b m x0 1 := by
    rw [xmX_succ]; unfold xmA; rw [xmX_zero]
    conv_lhs => rw [hx0v]
    exact (psi_mono hκ1 (add_le_add le_rfl (psi_mono hκ2 (add_le_add le_rfl (mul_le_mul_right hx0pos _))).1)).1
  have hm : ∀ n, m ∈ S.CSet (xmA S (A + 1) b m x0 n) (xmX S (A + 1) b m x0 (n + 1)) := fun n =>
    hmC _ _ (hex0.trans_le (xmX_monotone h0 (Nat.zero_le (n + 1))))
  have hm2 : ∀ a, m ∈ S.CSet a (S.psi a (Om (1 + 1))) := fun a =>
    hmC _ _ ((hex0.trans hx01).trans (psiS_bounds (S := S) _ 1).1)
  have hplat := xmPlat (S := S) (B := A + 1) hbn hm2 h0 hx01 hm
  have hdom : ∀ n, xmX S (A + 1) b m x0 n ≤ gxTh (upsilon l) (ldAtR S l) (u (n + 1)) :=
    xmX_le (y := fun n => gxTh (upsilon l) (ldAtR S l) (u (n + 1))) le_rfl fun n => by
      show _ ≤ gxTh (upsilon l) (ldAtR S l) (u (n + 1 + 1))
      rw [hΘu (n + 1), hMe]
      exact (psi_mono hκ1 (add_le_add le_rfl (psi_mono hκ2 (add_le_add le_rfl
        (mul_le_mul_right le_self_add _))).1)).1
  have hus : ∀ n, u (n + 1) ≤ leTe S (X + (e + 1)) β := fun n => by
    unfold leTe
    rw [hw2]
    show S.psi (β + w * u n + w) (Om (1 + 1)) ≤ _
    refine (psi_mono hκ2 ?_).1
    rw [add_assoc, ← mul_add_one]
    exact add_le_add le_rfl (leMulWe_mono (Order.add_one_le_of_lt (hu2 n)))
  have hlow : S.psi (A + 1 + S.psi (b + ω ^ m * Om 1) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (leTe S (X + (e + 1)) β) :=
    hplat.trans (ciSup_le fun n => (hdom n).trans (gxTh_mono (hus n)))
  -- the upper half
  have hD1 : VbD S l (β + leWe (X + (e + 1))) := by
    rw [← add_assoc]
    exact ⟨CSet.add_mem hβH (leWe_mem hg1D.1), CSet.add_mem hβD.2.1 (leWe_mem hg1D.2.1),
      vkOmW.1.isPrincipal hβW (leWe_lt_SC vkOmW.1 vkOmW.2 hg1W).1⟩
  have hup := Xd.xdUp_at hl hX hA hρ _ hD1
  rw [hTtop]
  rw [hTtop] at hup
  exact le_antisymm hup hlow

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Xm

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmU_it
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmSucc
