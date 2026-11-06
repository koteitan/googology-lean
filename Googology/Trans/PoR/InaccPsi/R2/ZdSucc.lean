import Googology.Trans.PoR.InaccPsi.R2.XmLim

/-!
# THE SUCCESSOR AND LIMIT STEPS of the top law, GENERIC IN THE SHIFT

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `W^x = leWe x`, `Ω^x = leOe x`.

`Xm.xmSucc` / `Xm.xmLim` are written for the shift `X = Ω_{k+3}` only.  Here the shift is a parameter `X` with the
data `ZdSh S λ X K`: `X` lies in every closure `Cl(a, c)` with `Ω₁ ≤ c` and in `H_λ`, `X < Ω_ω`, `T X = K`, `K` and
`Ω₁·K` lie in every closure `Cl(a, c)` with `ρ_λ ≤ c`, `0 < K` (round 140: these thresholds, in place of every
closure, let the shift carry a countable coefficient `ξ < ρ_λ`, `zdSh_cnt`).
The law at the exponent `X + e` over a base `β` is

  `ZdLaw S λ A X e β :  Θ(ψ₂(β + W^{X+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+e})))`.

* `zdSucc` (**THE SUCCESSOR STEP**: the law at `e` on every base of exponent `e` gives the law at `e + 1`),
* `zdLim` (**THE LIMIT STEP**: the law at every code `e' < e` gives the law at the limit code `e`),
* `zdTopUp` (**the law at every code**, given the law at `e = 0`).

Round 141: `ZdShQ S λ X K q` is the shift data with a THRESHOLD CODE `q` (`X ∈ Cl(a, c)` once `Ω₁ ≤ c`, `q < c`;
`K`, `Ω₁·K ∈ Cl(a, c)` once `ρ_λ ≤ c`, `Θ q < c`; `q < θ` a code), so the shift may carry an uncountable
coefficient; `ZdSh` is the case `q = 0` (`ZdSh.toQ`).  `zdSuccQ`, `zdLimQ`, `zdTopUpQ` are the steps for `ZdShQ`
on the bases with a condition `Q` (upward closed, `Q β ⇒ q < ψ₂(β + W^X)`, which puts `Θ q` below the first
plateau iterate); `zdSucc`, `zdLim`, `zdTopUp` are their instances `q = 0`, `Q = True`.

`Xm.xmSucc`, `Xm.xmLim`, `Xm.xmTopUp` are the instance `X = Ω_{k+3}`, `K = Ω_{k+2}` (`zdSh_Om`).

No new axiom.  New definitions: `ZdSh`, `ZdShQ` (the shift data), `ZdLaw` (the statement of the law; abbreviations).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm

variable {S : InaccSeq.{0}}

/-- **A shift in every closure**: `X ∈ Cl(a, c)` for all `a, c`, `X < Ω_ω`, `T X = K`, `K`, `Ω₁·K` in every
closure, `0 < K`. -/
structure ZdSh (S : InaccSeq.{0}) (l X K : Ordinal.{0}) : Prop where
  mem : ∀ a c : Ordinal.{0}, Om 1 ≤ c → X ∈ S.CSet a c
  lt : X < Om ω
  T : vbT S l X = K
  Km : ∀ a c : Ordinal.{0}, upsilon l ≤ c → K ∈ S.CSet a c
  Km1 : ∀ a c : Ordinal.{0}, upsilon l ≤ c → Om 1 * K ∈ S.CSet a c
  Kpos : 0 < K
  memH : X ∈ cdHull S l

/-- The top law at the exponent `X + e` over the base `β`. -/
def ZdLaw (S : InaccSeq.{0}) (l A X e β : Ordinal.{0}) : Prop :=
  gxTh (upsilon l) (ldAtR S l) (leTe S (X + e) β) =
    S.psi (A + 1 + S.psi (vbT S l (β + leWe (X + e))) (Om (1 + 1))) (Om 1)

theorem zd_Om1_le_th : Om 1 ≤ ConjT.th S := (psiS_bounds (S := S) _ 1).1.le

theorem ZdSh.D {l X K : Ordinal.{0}} (hs : ZdSh S l X K) : VbD S l X := ⟨hs.memH, hs.mem _ _ zd_Om1_le_th, hs.lt⟩

/-- **A shift with a threshold code `q`** (round 141): `X ∈ Cl(a, c)` for `Ω₁ ≤ c`, `q < c`; `K`, `Ω₁·K` in
`Cl(a, c)` for `ρ_λ ≤ c`, `Θ q < c`; `q` a code below `θ`.  `ZdSh` is the case `q = 0` (`ZdSh.toQ`). -/
structure ZdShQ (S : InaccSeq.{0}) (l X K q : Ordinal.{0}) : Prop where
  mem : ∀ a c : Ordinal.{0}, Om 1 ≤ c → q < c → X ∈ S.CSet a c
  lt : X < Om ω
  T : vbT S l X = K
  Km : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c → K ∈ S.CSet a c
  Km1 : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c → Om 1 * K ∈ S.CSet a c
  Kpos : 0 < K
  memH : X ∈ cdHull S l
  qc : GxCl (upsilon l) (ldAtR S l) q
  qθ : q < ConjT.th S

theorem ZdSh.toQ {l X K : Ordinal.{0}} (hs : ZdSh S l X K) (h0 : 0 < upsilon l) : ZdShQ S l X K 0 :=
  ⟨fun a c h _ => hs.mem a c h, hs.lt, hs.T, fun a c h _ => hs.Km a c h, fun a c h _ => hs.Km1 a c h, hs.Kpos,
    hs.memH, GxCl.zero h0, (ConjT.SC_th S).1⟩

theorem ZdShQ.D {l X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) : VbD S l X :=
  ⟨hs.memH, hs.mem _ _ zd_Om1_le_th hs.qθ, hs.lt⟩

/-- `Ω_{k+3}` is such a shift, with `K = Ω_{k+2}`. -/
theorem zdSh_Om {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ) :
    ZdSh S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  have hK2ε : ω ^ Om ((k : Ordinal.{0}) + 1 + 1) = Om ((k : Ordinal.{0}) + 1 + 1) :=
    gg_SC_eps (SC_Om (Xi.xiNe k 1))
  have hOK : Om 1 * Om ((k : Ordinal.{0}) + 1 + 1) = veblen 0 (Om 1 + Om ((k : Ordinal.{0}) + 1 + 1)) := by
    rw [veblen_zero_apply, opow_add, Om1_opow, hK2ε]
  refine ⟨fun a c _ => Vn.vnOmK3_mem k a c, Wv.wvOmK_lt_W k, ?_, fun a c _ => CSet.Om_mem (CSet.succ_mem
    (CSet.succ_mem (Sc.scNat_mem a c k))), fun a c _ => ?_, Om_pos (Xi.xiNe k 1), Vn.vnOmK3_mem k _ _⟩
  · have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [Xi.xiC2] at h
  · rw [hOK]
    exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (Sc.scNat_mem a c k)))))

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE SUCCESSOR STEP, GENERIC IN THE SHIFT**: the law at the exponent `X + e` on every base of exponent `e`
gives the law at `X + (e + 1)`. -/
theorem zdSuccQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hB : Ro.RoBaseE S l X (e + 1) β)
    (hq : q < S.psi (β + leWe X) (Om (1 + 1)))
    (IH : ∀ β', VbD S l β' → Ro.RoBaseE S l X e β' → β ≤ β' → ZdLaw S l A X e β') :
    ZdLaw S l A X (e + 1) β := by
  unfold ZdLaw at IH ⊢
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  set w := leWe (X + e) with hwdef
  have hXW : X < Om ω := hs.lt
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
  have hgH : X + e ∈ cdHull S l := CSet.add_mem hs.memH heH
  have hgC : X + e ∈ S.CSet (Om ω) (ConjT.th S) :=
    CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) (CSet.of_lt heθ)
  have hqw : q < S.psi (β + w) (Om (1 + 1)) :=
    hq.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1
  have hgD : VbD S l (X + e) := ⟨hgH, hgC, hgW⟩
  have hg1D : VbD S l (X + e + 1) := ⟨CSet.succ_mem hgH, CSet.succ_mem hgC, hg1W⟩
  -- the iterates
  set u := xmU S β w with hudef
  have hgA : ∀ a, β + w ≤ a → X + e ∈ S.CSet a (S.psi a (Om (1 + 1))) := fun a ha =>
    CSet.add_mem (hs.mem _ _ (psiS_bounds (S := S) _ 1).1.le (hqw.trans_le (psi_mono hκ2 ha).1))
      (CSet.of_lt (hexp.trans_le (psi_mono hκ2 ha).1))
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
    have h := IH _ (hβnD n) (hβnB n) le_self_add
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
  have hTg : vbT S l (X + e) = K + gxTh (upsilon l) (ldAtR S l) e := by
    rw [Vh.vhT_add hl hX hs.D ⟨heH, CSet.of_lt heθ, heW.trans ldOm2_lt_OmW⟩, vbT_code hl hX heW heH, hs.T]
  have hmC : ∀ a c, gxTh (upsilon l) (ldAtR S l) e < c → upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) q < c →
      m ∈ S.CSet a c := by
    intro a c hc hρc hqc
    rw [hmdef, hTg, mul_add]
    exact CSet.add_mem (hs.Km1 a c hρc hqc) (mem_Om1_mul hc)
  have hu1 : u 1 = S.psi (β + w) (Om (1 + 1)) := by
    show S.psi (β + w * xmU S β w 0 + w) (Om (1 + 1)) = _
    rw [xmU_zero, mul_zero, add_zero]
  set x0 := gxTh (upsilon l) (ldAtR S l) (u 1) with hx0def
  have hex0 : gxTh (upsilon l) (ldAtR S l) e < x0 := gxTh_lt hec (by rw [hu1]; exact hexp)
  have hqx0 : gxTh (upsilon l) (ldAtR S l) q < x0 := gxTh_lt hs.qc (by rw [hu1]; exact hqw)
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
  have hρx0 : upsilon l ≤ x0 := by
    rw [hx0v, ← hρ]; exact (psi_mono hκ1 (le_self_add.trans le_self_add)).1
  have hm : ∀ n, m ∈ S.CSet (xmA S (A + 1) b m x0 n) (xmX S (A + 1) b m x0 (n + 1)) := fun n =>
    hmC _ _ (hex0.trans_le (xmX_monotone h0 (Nat.zero_le (n + 1))))
      (hρx0.trans (xmX_monotone h0 (Nat.zero_le (n + 1)))) (hqx0.trans_le (xmX_monotone h0 (Nat.zero_le (n + 1))))
  have hm2 : ∀ a, m ∈ S.CSet a (S.psi a (Om (1 + 1))) := fun a =>
    hmC _ _ ((hex0.trans hx01).trans (psiS_bounds (S := S) _ 1).1) (hρ1.trans (psiS_bounds (S := S) _ 1).1).le
      ((hqx0.trans hx01).trans (psiS_bounds (S := S) _ 1).1)
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

/-- **THE LIMIT STEP, GENERIC IN THE SHIFT**: the law at every code `e' < e` over the base `β` gives the law at the
limit code `e`. -/
theorem zdLimQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hlim : IsSuccLimit e) (hβD : VbD S l β) (hB : Ro.RoBaseE S l X e β)
    (IH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e → ZdLaw S l A X e' β) :
    ZdLaw S l A X e β := by
  unfold ZdLaw at IH ⊢
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hXW : X < Om ω := hs.lt
  obtain ⟨-, hβH, -, -, hexpA⟩ := hB
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt hκ2 _)
  have hβW : β < Om ω := hβD.2.2
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (heW.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  -- `T(β + W^{X+c}) = T β + Ω^{K+Θc}` for every code `c ≤ e`
  have hTc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ e →
      vbT S l (β + leWe (X + c)) = vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) c) := by
    intro c hc hce
    have hcW : c < Om (1 + 1) := hce.trans_lt heW
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hcθ : c < ConjT.th S := hce.trans_lt heθ
    have hcD : VbD S l c := ⟨hcH, CSet.of_lt hcθ, hcW.trans ldOm2_lt_OmW⟩
    have hgcW : X + c < Om ω := vkOmW.1.isPrincipal hXW (hcW.trans ldOm2_lt_OmW)
    have hgD : VbD S l (X + c) :=
      ⟨CSet.add_mem hs.memH hcH, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) (CSet.of_lt hcθ), hgcW⟩
    have e1 : leWe (X + c) = leWe (X + c) * 1 + 0 := by rw [mul_one, add_zero]
    have hD1 : VbD S l (leWe (X + c) * 1 + 0) := by
      rw [mul_one, add_zero]
      exact ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgcW).1⟩
    rw [e1, Vh.vhT_add hl hX hβD hD1, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.one_mem _ _)
      (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one,
      Vh.vhT_add hl hX hs.D hcD, hs.T, vbT_code hl hX hcW hcH]
  have he0 : (0 : Ordinal.{0}) < e := pos_iff_ne_zero.2 hlim.ne_bot
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  -- the upper half
  have hD : VbD S l (β + leWe (X + e)) :=
    ⟨CSet.add_mem hβH (leWe_mem (CSet.add_mem hs.memH ((ldHull_iff hl hX heW).2 hec))),
      CSet.add_mem hβD.2.1 (leWe_mem (CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) (CSet.of_lt heθ))),
      vkOmW.1.isPrincipal hβW hwW⟩
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold leTe
  refine le_antisymm hup ?_
  -- the lower half
  set s := S.psi (β + leWe (X + e)) (Om (1 + 1)) with hsdef
  have hread : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < e →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) c)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) s := by
    intro c hc hce
    have h := IH c hc hce
    unfold leTe at h
    rw [hTc c hc hce.le] at h
    rw [← h]
    exact gxTh_mono (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add le_rfl hce.le)))).1
  have hΘe0 : 0 < gxTh (upsilon l) (ldAtR S l) e := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c he0; rwa [gxTh_zero] at this
  have hΘlim := xmTh_lim hl hX heW hlim
  rw [hTc e hec le_rfl]
  set L := vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) e) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hr0 := hread 0 h0c he0
  rw [gxTh_zero, add_zero] at hr0
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0
      (mul_pos (Om_pos one_ne_zero) (lt_of_lt_of_le hs.Kpos le_self_add)).ne')
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    obtain ⟨y', hy', hzy⟩ := xmCofL hΘe0 hΘlim z.2
    obtain ⟨c, hc, hce, hcy⟩ := gxTh_onto hy'
    have h2 := hread c hc hce
    rw [hcy] at h2
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzy.le).1))).1.trans h2

/-- **THE LAW AT EVERY CODE, GENERIC IN THE SHIFT AND IN A BASE CONDITION `Q`**: `Q` is upward closed and gives
`q < ψ₂(β + W^X)`; given the law at `X + 0` on every base of exponent `0` with `Q`, the law at `X + e` holds on
every base of exponent `e` with `Q`, for every code `e < Ω₂`. -/
theorem zdTopUpQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) (Q : Ordinal.{0} → Prop)
    (hQq : ∀ β, Q β → q < S.psi (β + leWe X) (Om (1 + 1))) (hQup : ∀ β β', β ≤ β' → Q β → Q β')
    (H0 : ∀ β, VbD S l β → Ro.RoBaseE S l X 0 β → Q β → ZdLaw S l A X 0 β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β → Q β →
      ZdLaw S l A X e β := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IHe =>
  intro hec he2 β hβD hB hQ
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e', he'⟩ | hlim
  · subst h0
    exact H0 β hβD hB hQ
  · rw [succ_eq_add_one] at he'
    subst he'
    have he'2 : e' < Om (1 + 1) := (lt_add_one e').trans he2
    have hec' : GxCl (upsilon l) (ldAtR S l) e' :=
      (ldHull_iff hl hX he'2).1 (mem_of_add_one_mem ((ldHull_iff hl hX he2).2 hec))
    exact zdSuccQ hl hX hA hρ hs hec' hβD hB (hQq β hQ) fun β' hβ'D hB' hle =>
      IHe e' (lt_add_one e') hec' he'2 β' hβ'D hB' (hQup β β' hle hQ)
  · exact zdLimQ hl hX hA hρ hs hec hlim hβD hB fun e' hc' hlt =>
      IHe e' hlt hc' (hlt.trans he2) β hβD (Ro.roBaseE_mono hlt.le hB) hQ

/-- **THE SUCCESSOR STEP** for a shift of `ZdSh` (`zdSuccQ` at `q = 0`). -/
theorem zdSucc {X K : Ordinal.{0}} (hs : ZdSh S l X K) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l X (e + 1) β)
    (IH : ∀ β', VbD S l β' → Ro.RoBaseE S l X e β' → ZdLaw S l A X e β') :
    ZdLaw S l A X (e + 1) β :=
  zdSuccQ hl hX hA hρ (hs.toQ (leRho hl hX).1.1) hec hβD hB (SC_psi (InR_Om_succ 1) _).1
    fun β' hβ'D hB' _ => IH β' hβ'D hB'

/-- **THE LIMIT STEP** for a shift of `ZdSh` (`zdLimQ` at `q = 0`). -/
theorem zdLim {X K : Ordinal.{0}} (hs : ZdSh S l X K) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hlim : IsSuccLimit e) (hβD : VbD S l β) (hB : Ro.RoBaseE S l X e β)
    (IH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e → ZdLaw S l A X e' β) :
    ZdLaw S l A X e β :=
  zdLimQ hl hX hA hρ (hs.toQ (leRho hl hX).1.1) hec hlim hβD hB IH

/-- **THE LAW AT EVERY CODE, GENERIC IN THE SHIFT**: given the law at the exponent `X + 0` on every base of
exponent `0`, the law at `X + e` holds on every base of exponent `e`, for every code `e < Ω₂`. -/
theorem zdTopUp {X K : Ordinal.{0}} (hs : ZdSh S l X K)
    (H0 : ∀ β, VbD S l β → Ro.RoBaseE S l X 0 β → ZdLaw S l A X 0 β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β →
      ZdLaw S l A X e β := fun e hec he2 β hβD hB =>
  zdTopUpQ hl hX hA hρ (hs.toQ (leRho hl hX).1.1) (fun _ => True) (fun _ _ => (SC_psi (InR_Om_succ 1) _).1)
    (fun _ _ _ _ => trivial) (fun β hβD hB _ => H0 β hβD hB) e hec he2 β hβD hB trivial

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Zd
