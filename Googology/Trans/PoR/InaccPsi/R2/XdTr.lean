import Googology.Trans.PoR.InaccPsi.R2.WzUp

/-!
# `T` on the closures `Cl(a, b)`: the transfer lemma

`T = Vb.vbT S λ` (the image one level down), `D = Vb.VbD S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`.

* `xdT_cl` (**THE GENERIC TRANSFER**): let `b ≤ Ω₂`, and let `a', b'` be such that `T e < a'` for every `e ∈ D`,
  `e < a`, and `T c ∈ Cl(a', b')` for every code `c ∈ D`, `c < Ω₂`, `c ∈ Cl(a, b)`.  Then every `x ∈ D ∩ Cl(a, b)`
  has `T x ∈ Cl(a', b')`.  One induction on the normal-form measure of `Rx` (Cantor normal form, Veblen nodes,
  `Ω_k`, atoms `ψ_{Ω_{k+1}}(d)`; an atom `≥ Ω₂ ≥ b` of `Cl(a, b)` has its normal argument in `Cl(a, b)` below `a`);
* `xdTr` (**the transfer**): `a ∈ D`, `x ∈ D`, `x ∈ Cl(a, ψ₂(a))` ⇒ `T x ∈ Cl(T a, ψ₂(T a))`;
* `xdT_psi_lt` (`ψ₂(d) < ψ₂(a)` for normal `d, a ∈ D` ⇒ `ψ₂(T d) < ψ₂(T a)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

theorem xdNat_mem (a b : Ordinal.{0}) : ∀ n : ℕ, ((n : Ordinal.{0})) ∈ S.CSet a b
  | 0 => by simpa using CSet.zero_mem (S := S) a b
  | n + 1 => by rw [Nat.cast_succ]; exact CSet.succ_mem (xdNat_mem a b n)

theorem xdOm2_le_Lam : Om (1 + 1 : Ordinal.{0}) ≤ S.Lam :=
  (lt_Lam_of_mem (S := S) (a := 0) zero_le
    (CSet.Om_mem (CSet.add_mem (CSet.one_mem (S := S) 0 0) (CSet.one_mem 0 0)))).le

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE GENERIC TRANSFER of `T` on closures.** -/
theorem xdT_cl {a b a' b' : Ordinal.{0}} (hb2 : b ≤ Om (1 + 1))
    (hTa : ∀ e, VbD S l e → e < a → vbT S l e < a')
    (hcode : ∀ c, VbD S l c → c < Om (1 + 1) → c ∈ S.CSet a b → vbT S l c ∈ S.CSet a' b') :
    ∀ x, VbD S l x → x ∈ S.CSet a b → vbT S l x ∈ S.CSet a' b' := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx hxC => ?_
  have hxE : RxE S (upsilon l) x := vbD_E hl hX hx
  rcases lt_or_ge x (Om (1 + 1)) with h2 | h2
  · exact hcode x hx h2 hxC
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 h2
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := vbT_Om hl hX (k := i) (by omega)
    rw [Nat.cast_succ, h]
    exact CSet.Om_mem (xdNat_mem _ _ i)
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne h2 (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hS : SC x
  · obtain ⟨k, hk, d, hdE, hdn, hxd, hst⟩ := rxE_atom hZ1.le hxE hS hx1 hΩ
    have hk2 : 2 ≤ k := by
      by_contra hc
      have hk1 : k = 1 := by omega
      subst hk1
      have := (psiS_bounds (S := S) d ((1 : ℕ) : Ordinal.{0})).2
      rw [Nat.cast_one] at this hxd
      rw [hxd] at hx2
      exact absurd (hx2.trans this) (lt_irrefl _)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : 1 ≤ k' := by omega
    have hdD : VbD S l d := vbD_atom hl hX (hxd ▸ hx) hdE hdn hk
    have hκ := InR_Om_succ (S := S) (((k' + 1 : ℕ) : Ordinal.{0}))
    obtain ⟨hdC, hda⟩ := arg_mem_of_psi_mem hκ (hxd ▸ hxC) (hb2.trans (h2.trans_eq hxd))
      (hb2.trans xdOm2_le_Lam) hdn
    have hTd := IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hst) hdD hdC
    have hdn' : d ∈ S.CSet d (S.psi d (Om ((k' : Ordinal.{0}) + 1 + 1))) := by
      have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
      rw [e] at hdn; exact hdn
    have hA := vbT_atom hl hX hk' hdD hdn'
    have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
    rw [hxd, e, hA.1]
    exact CSet.psi_mem (hTa d hdD hda) (InR_Om_succ _) (CSet.Om_mem (CSet.succ_mem (xdNat_mem _ _ k')))
      hTd
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hS
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbD_veb hx hxE hv hb
    obtain ⟨haC, hbC⟩ := rxCDecV hxC _ _ hv hb
    rw [vbT_veb hl hX hx hv ha0.ne' hb h2]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha) haD haC) (IH _ (rxMs_lt_val hhb hb) hbD hbC)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbD_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbD_rem hx hxE
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : x < ω ^ log ω x * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd (opow_log_le_self ω h0) (not_le.2 hlt)
    · exact h
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  have hlC : log ω x ∈ S.CSet a b := (rxCDec x hxC).2
  have hrC : x % ω ^ log ω x ∈ S.CSet a b := vbC_rem hxC
  have hTl := IH _ (rxMs_lt_val hlh hlx) hlD hlC
  have hTr := IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD hrC
  rw [(congrArg (vbT S l) hdm).trans (Vh.vhT_cnf hl hX n hn1 hlD hrD hs)]
  have hop : ω ^ vbT S l (log ω x) ∈ S.CSet a' b' := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hTl; rwa [veblen_zero_apply] at this
  exact CSet.add_mem (ConjT.mul_nat_mem S hop n) hTr

/-- **THE TRANSFER**: `x ∈ Cl(a, ψ₂(a))` ⇒ `T x ∈ Cl(T a, ψ₂(T a))` (`a, x ∈ D`). -/
theorem xdTr {a x : Ordinal.{0}} (ha : VbD S l a) (hx : VbD S l x)
    (hxC : x ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    vbT S l x ∈ S.CSet (vbT S l a) (S.psi (vbT S l a) (Om (1 + 1))) := by
  refine xdT_cl hl hX (psi_lt (InR_Om_succ 1) a).le (fun e he hea => vbT_mono hl hX he ha hea)
    (fun c hc hc2 _ => CSet.of_lt ?_) x hx hxC
  have h1 := vbT_lt_lev hl hX hc 0 (by simpa using hc2)
  simp only [Nat.cast_zero, zero_add] at h1
  exact h1.trans (psiS_bounds (S := S) (vbT S l a) 1).1

/-- **`ψ₂(d) < ψ₂(a)` with `d` normal ⇒ `ψ₂(T d) < ψ₂(T a)`** (`d, a ∈ D`). -/
theorem xdT_psi_lt {a d : Ordinal.{0}} (ha : VbD S l a) (hd : VbD S l d)
    (hdn : d ∈ S.CSet d (S.psi d (Om (1 + 1))))
    (hlt : S.psi d (Om (1 + 1)) < S.psi a (Om (1 + 1))) :
    S.psi (vbT S l d) (Om (1 + 1)) < S.psi (vbT S l a) (Om (1 + 1)) := by
  have hda : d < a := by
    by_contra hc
    exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 hc)).1)
  have hdC : d ∈ S.CSet a (S.psi a (Om (1 + 1))) := (psi_mono (S := S) (InR_Om_succ 1) hda.le).2 hdn
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (vbT_mono hl hX hd ha hda) (xdTr hl hX ha hd hdC)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Xd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdT_cl
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdTr
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xd.xdT_psi_lt
