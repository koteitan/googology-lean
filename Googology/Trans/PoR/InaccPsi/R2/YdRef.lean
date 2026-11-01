import Googology.Trans.PoR.InaccPsi.R2.YdBase

/-!
# REFUTE FIRST: the inverse correspondence fails at an atom code just above `B_n(ψ₂ t)`

The round-125 plan for the own clause of `Ro.RoBaseE` at `λ'` was the INVERSE CORRESPONDENCE: every code of `λ'`
below `B_n(ψ₂ t)` is `B_n` of a code of `λ` (enough for the atom codes).  It is FALSE, already at the base `0`, at
the atom `F = ψ₂(Ω_{k+3} + c_n)` (`c_n = L(n+1)`):

* `ydAtC` (`B_n ψ₂(X + c) = ψ₂(X + B_n c)` for `c < L(ω)`);
* `ydInvRef` (**at every window and every `k`: `F` is an atom (so a code) of `λ'`, `ψ₂(X) = B_n(ψ₂(W^X)) < F <
  ψ₂(W^{X+1})`, and `F ≠ B_n y` for EVERY `y` in the domain `MvD` of the base changes**: below `ψ₂(X + c_n)` the
  values `B_n y` stay below some `ψ₂(X + d)`, `d < c_n` (continuity of `ψ₂` at the limit `X + c_n`), and from
  `ψ₂(X + c_n)` on they are `≥ ψ₂(X + L(ω)) > F`).

So the inverse correspondence cannot be the road; `Yd.ydBaseMove` proves the base-data move at the base `0` without
it.  No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

theorem ydLw_lt_Om1 : Nc.ncL S ω < Om 1 := psi_lt Low.InR_Om_one _

/-- `X + c` is normal at the level `Ω₂` for countable `c`. -/
theorem ydXc_own (k : ℕ) {c : Ordinal.{0}} (hc : c < Om 1) (a : Ordinal.{0}) :
    Om ((k : Ordinal.{0}) + 1 + 1 + 1) + c ∈ S.CSet a (S.psi a (Om (1 + 1))) :=
  CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt (hc.trans (psiS_bounds (S := S) a 1).1))

/-- **`B_n ψ₂(X + c) = ψ₂(X + B_n c)` for `c < L(ω)`.** -/
theorem ydAtC (k n : ℕ) {c : Ordinal.{0}} (hc : c < Nc.ncL S ω) :
    MvD S (S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + c) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + c) (Om (1 + 1))) =
        S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n c) (Om (1 + 1)) := by
  have hs : (k : Ordinal.{0}) + 1 + 1 < ω := (lt_add_one _).trans (vkNat_lt_omega k)
  obtain ⟨hDX, hBX⟩ := Vs.vsW_D (S := S) hs (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDX (mvD_of_lt hc)
  obtain ⟨hD, hBs⟩ := mxB_atom (n := n) hDa (ydXc_own k (hc.trans ydLw_lt_Om1) _)
  rw [hBa, hBX] at hBs
  exact ⟨hD, hBs⟩

theorem ydPsiXc_lt (k : ℕ) {c d : Ordinal.{0}} (hcd : c < d) (hd : d < Om 1) :
    S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + c) (Om (1 + 1)) <
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + d) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 hcd) (ydXc_own k (hcd.trans hd) _)

/-- **REFUTED: the inverse correspondence at the atom code `F = ψ₂(Ω_{k+3} + c_n)` of `λ'`.** -/
theorem ydInvRef {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (k : ℕ) :
    S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) (Om (1 + 1))) =
        S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ∧
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) <
        S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) ∧
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) <
        S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 1)) (Om (1 + 1)) ∧
      ∀ y, MvD S y → Bc.bcB S n y ≠ S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set c := Bc.bcC S n with hcdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hcLw : c < Nc.ncL S ω := Bc.bcC_lt S n
  have hc1 : c < Om 1 := hcLw.trans ydLw_lt_Om1
  have hcSC : SC c := Lw.lw_L_SC S _
  -- `c_n < ρ_{λ'}`
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hρLw : upsilon l < Nc.ncL S ω := h2.trans (Bc.bcC_lt S (n + 1))
  have hBc : Bc.bcB S n c = Nc.ncL S ω := Bc.bcB_base (S := S) n
  have hcρ' : c < upsilon l' := by
    have h := (mvB_lt_iff (k := n) (mvD_of_lt hcLw) (mvD_of_lt hρLw)).2 h1
    rw [hBc, hB] at h
    exact hcLw.trans h
  -- the atom
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hXcW : X + c < Om ω := vkOmW.1.isPrincipal hXW (hc1.trans (Om_lt_Om.2 one_lt_omega0))
  have hat : S.psi (X + c) (Om (1 + 1)) ∈ ldAtR S l' :=
    ⟨X + c, CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt hcρ'), hXcW.trans_le (ConjT.OmW_le_A S _), rfl⟩
  -- `B_n ψ₂(W^X) = ψ₂(X)`
  have hs : (k : Ordinal.{0}) + 1 + 1 < ω := (lt_add_one _).trans (vkNat_lt_omega k)
  obtain ⟨hDX, hBX⟩ := Vs.vsW_D (S := S) hs (n := n)
  obtain ⟨-, hBY⟩ := mxB_atom (n := n) hDX (Vn.vnOmK3_mem k _ _)
  rw [hBX] at hBY
  have hW : leWe X = X := Vn.vnWe_OmK k
  -- `ψ₂(X) < F`
  have hlow : S.psi X (Om (1 + 1)) < S.psi (X + c) (Om (1 + 1)) := by
    have h := ydPsiXc_lt (S := S) k hcSC.1 hc1
    rwa [add_zero] at h
  -- `F < ψ₂(W^{X+1})`
  have hup : S.psi (X + c) (Om (1 + 1)) < S.psi (leWe (X + 1)) (Om (1 + 1)) := by
    have hW1 : leWe (X + 1) = X * Om (1 + 1) := by
      unfold leWe
      rw [mul_add, mul_one, opow_add, gg_SC_eps ldOm2_SC]
      congr 1
    have hcX : c < X := hc1.trans ((Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0}))).trans (Vn.vnOm2_lt_K k))
    have hlt : X + c < leWe (X + 1) := by
      rw [hW1]
      calc X + c < X + X := (add_lt_add_iff_left X).2 hcX
        _ = X * 2 := by rw [← one_add_one_eq_two, mul_add, mul_one]
        _ ≤ X * Om (1 + 1) := mul_le_mul_right (by
            exact (natCast_lt_omega0 2).le.trans (Lw.lw_omega_lt_SC ldOm2_SC).le) X
    exact psi_lt_psi_of_mem hκ2 hlt (ydXc_own k hc1 _)
  refine ⟨hat, by rw [hW]; exact hBY, hlow, hup, ?_⟩
  -- no `B_n`-preimage
  intro y hy hEq
  obtain ⟨hD0, hB0⟩ := ydAtC (S := S) k n hcLw
  rw [hBc] at hB0
  rcases lt_or_ge y (S.psi (X + c) (Om (1 + 1))) with hlt | hge
  · -- continuity at the limit `X + c`
    have hlim : IsSuccLimit (X + c) := isSuccLimit_add X hcSC.isSuccLimit
    have hsup := Lw.lw_psi_limit S hκ2 hlim
    haveI : Nonempty (Iio (X + c)) := ⟨⟨0, hlim.bot_lt⟩⟩
    have hbdd : BddAbove (range fun e : Iio (X + c) => S.psi e.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
    rw [hsup] at hlt
    obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hlt
    obtain ⟨d, hdc, hed⟩ := (Ordinal.lt_add_iff hcSC.1.ne').1 e.2
    have hyd : y < S.psi (X + d) (Om (1 + 1)) := he.trans_le (psi_mono hκ2 hed).1
    obtain ⟨hDd, hBd⟩ := ydAtC (S := S) k n (hdc.trans hcLw)
    rw [Bc.bcB_fix' S n d hdc] at hBd
    have h := (mvB_lt_iff (k := n) hy hDd).2 hyd
    rw [hBd, hEq] at h
    exact absurd (h.trans (ydPsiXc_lt k hdc hc1)) (lt_irrefl _)
  · have h := (not_lt.2 hge)
    rw [← mvB_lt_iff (k := n) hy hD0, not_lt, hB0, hEq] at h
    have hcL : c < Nc.ncL S ω := hcLw
    exact absurd ((ydPsiXc_lt k hcL ydLw_lt_Om1).trans_le h) (lt_irrefl _)

end Googology.Trans.PoR.InaccPsi.R2.Yd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydAtC
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydInvRef
