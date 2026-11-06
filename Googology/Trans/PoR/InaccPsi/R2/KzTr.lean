import Googology.Trans.PoR.InaccPsi.R2.KzAdd

/-!
# Kz: `T_K` ON THE CLOSURES (`Xd.xdT_cl`, `Xd.xdTr`, `Xd.xdT_psi_lt` below a bound `K`)

* `kzT_cl` (**THE GENERIC TRANSFER BELOW `K`**: the new case `x = Ω_ω`, `T_K Ω_ω = Ω_ω`), `kzTr` (**`x ∈ Cl(a, ψ₂ a)
  ⇒ T_K x ∈ Cl(T_K a, ψ₂(T_K a))`**), `kzT_psi_lt`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru
  Googology.Trans.PoR.InaccPsi.R2.Xd

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **THE GENERIC TRANSFER of `T` on closures.** -/
theorem kzT_cl {a b a' b' : Ordinal.{0}} (hb2 : b ≤ Om (1 + 1))
    (hTa : ∀ e, VbDK S l K e → e < a → vbTK S l K e < a')
    (hcode : ∀ c, VbDK S l K c → c < Om (1 + 1) → c ∈ S.CSet a b → vbTK S l K c ∈ S.CSet a' b') :
    ∀ x, VbDK S l K x → x ∈ S.CSet a b → vbTK S l K x ∈ S.CSet a' b' := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx hxC => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  rcases lt_or_ge x (Om (1 + 1)) with h2 | h2
  · exact hcode x hx h2 hxC
  by_cases hxW : x = Om ω
  · rw [hxW, vbTK_OmW hl hX hKB (by rw [← hxW]; exact hx.2.2)]; exact ConjT.OmW_mem S _ _
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 2 ≤ j := by
      have h := Om_le_Om.1 h2
      rw [one_add_one_eq_two] at h
      have h' : ((2 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_ofNat]; exact h
      exact_mod_cast h'
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := vbTK_Om hl hX hKB (k := i) (by omega)
    rw [Nat.cast_succ, h]
    exact CSet.Om_mem (xdNat_mem _ _ i)
  have hx2 : Om (1 + 1) < x := lt_of_le_of_ne h2 (fun e => hΩ ⟨2, by rw [← e]; norm_num⟩)
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans hx2
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hS : SC x
  · obtain ⟨k, hk, d, hdE, hdn, hxd, hst⟩ := kzE_atom hKB hZ1.le hxE hS hx1 (kzNe hKB hxE hΩ hxW)
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
    have hdD : VbDK S l K d := vbDK_atom hl hX (hxd ▸ hx) hdE hdn hk
    have hκ := InR_Om_succ (S := S) (((k' + 1 : ℕ) : Ordinal.{0}))
    obtain ⟨hdC, hda⟩ := arg_mem_of_psi_mem hκ (hxd ▸ hxC) (hb2.trans (h2.trans_eq hxd))
      (hb2.trans xdOm2_le_Lam) hdn
    have hTd := IH d (rxMs_lt_stage (kzE_lt_Lam hKB hdE) hst) hdD hdC
    have hdn' : d ∈ S.CSet d (S.psi d (Om ((k' : Ordinal.{0}) + 1 + 1))) := by
      have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
      rw [e] at hdn; exact hdn
    have hA := vbTK_atom hl hX hKB hk' hdD hdn'
    have e : ((k' + 1 : ℕ) : Ordinal.{0}) = (k' : Ordinal.{0}) + 1 := Nat.cast_succ k'
    rw [hxd, e, hA.1]
    exact CSet.psi_mem (hTa d hdD hda) (InR_Om_succ _) (CSet.Om_mem (CSet.succ_mem (xdNat_mem _ _ k')))
      hTd
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hS
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
    obtain ⟨haC, hbC⟩ := rxCDecV hxC _ _ hv hb
    rw [vbTK_veb hl hX hKB hx hv ha0.ne' hb h2]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha) haD haC) (IH _ (rxMs_lt_val hhb hb) hbD hbC)
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
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
  rw [(congrArg (vbTK S l K) hdm).trans (kzT_cnf hl hX hKB n hn1 hlD hrD hs)]
  have hop : ω ^ vbTK S l K (log ω x) ∈ S.CSet a' b' := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hTl; rwa [veblen_zero_apply] at this
  exact CSet.add_mem (ConjT.mul_nat_mem S hop n) hTr

/-- **THE TRANSFER**: `x ∈ Cl(a, ψ₂(a))` ⇒ `T x ∈ Cl(T a, ψ₂(T a))` (`a, x ∈ D`). -/
theorem kzTr {a x : Ordinal.{0}} (ha : VbDK S l K a) (hx : VbDK S l K x)
    (hxC : x ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    vbTK S l K x ∈ S.CSet (vbTK S l K a) (S.psi (vbTK S l K a) (Om (1 + 1))) := by
  refine kzT_cl hl hX hKB (psi_lt (InR_Om_succ 1) a).le (fun e he hea => vbTK_mono hl hX hKB he ha hea)
    (fun c hc hc2 _ => CSet.of_lt ?_) x hx hxC
  have h1 := vbTK_lt_lev hl hX hKB hc 0 (by simpa using hc2)
  simp only [Nat.cast_zero, zero_add] at h1
  exact h1.trans (psiS_bounds (S := S) (vbTK S l K a) 1).1

/-- **`ψ₂(d) < ψ₂(a)` with `d` normal ⇒ `ψ₂(T d) < ψ₂(T a)`** (`d, a ∈ D`). -/
theorem kzT_psi_lt {a d : Ordinal.{0}} (ha : VbDK S l K a) (hd : VbDK S l K d)
    (hdn : d ∈ S.CSet d (S.psi d (Om (1 + 1))))
    (hlt : S.psi d (Om (1 + 1)) < S.psi a (Om (1 + 1))) :
    S.psi (vbTK S l K d) (Om (1 + 1)) < S.psi (vbTK S l K a) (Om (1 + 1)) := by
  have hda : d < a := by
    by_contra hc
    exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 hc)).1)
  have hdC : d ∈ S.CSet a (S.psi a (Om (1 + 1))) := (psi_mono (S := S) (InR_Om_succ 1) hda.le).2 hdn
  exact psi_lt_psi_of_mem (InR_Om_succ 1) (vbTK_mono hl hX hKB hd ha hda) (kzTr hl hX hKB ha hd hdC)

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
