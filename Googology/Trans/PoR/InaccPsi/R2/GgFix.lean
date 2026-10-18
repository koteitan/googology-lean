import Googology.Trans.PoR.InaccPsi.R2.GgOtp
import Googology.Trans.PoR.InaccPsi.R2.FxIso
import Googology.Trans.PoR.InaccPsi.R2.RzName

/-!
# The names `η₁ + ω^c` with `c ≥ Ω₁`: fixed points of `υ`, the prefix of a name, and the cofinal names

`P(η) = ψ_{Ω₁}(A_η) = υ_{ι(η)}` (Theorem GEN), `e(η) = cdExp η` the last exponent.

* `ggHCl_mul_nat`, `gg_opow_lim`;
* `ggPrefixE` (**the prefix of a good name is good**): `η₀ + ω^e` good, `ω^e ∣ η₀` ⟹ `η₀` good (by the window
  plateau `Nn.nnWPlat`, some `η₀ + y''`, `y'' ≤ ω^e`, is in `HCl(A_{η₀}, P(η₀))`; its prefix `η₀` is too, by
  `Nn.nnHCl_pre` and the last exponent `Gg.ggExp_HCl`);
* `ggFix` (**a limit `L` with `ζ + Ω₁ ≤ L` for all `ζ < L` has a fixed point `ι(L) = υ_{ι(L)}` of `υ` as index**):
  every index `i' < ι(L)` has a good name `η'`, and `ι(η' + P(η')) = i' + P(η') ≥ υ_{i'}` with `η' + P(η') < L`;
  the least `ζ` with `ι(ζ) = ι(L)` is a limit, so `υ_{ι(L)} = sup υ_{i'} ≤ ι(L)`;
* `ggCof` (**THE COFINAL NAMES**): at a named fixed point `F` of `υ` and a code `c` over `Z < F` with
  `Ω₁ ≤ c < e(η_F)`, every `ν < F` has a fixed point `μ = ι(η₁ + ω^c)` of `υ` with `ν < μ < F`, `Z ≤ μ` and
  `e(η_μ) = c`;
* `ggWin` (**the window**): with `η_F = η₀ + ω^{e(η_F)}`, every named restart `μ` with `ι(η₀) < μ < F` has
  `e(η_μ) < e(η_F)`, and `ι(η₀) < F`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

theorem ggHCl_mul_nat {a Z x : Ordinal.{0}} (h : HCl S a Z x) : ∀ n : ℕ, HCl S a Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact HCl.zero
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact HCl.add (ggHCl_mul_nat h n) h

theorem gg_opow_lim {c : Ordinal.{0}} (hc : c ≠ 0) : IsSuccLimit (ω ^ c) := by
  have e : ω ^ c = ω * ω ^ (c - 1) := by
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hc)]
    rw [opow_add, opow_one]
  rw [e]
  exact isSuccLimit_mul_left isSuccLimit_omega0 (opow_pos _ omega0_pos)

/-- **The prefix of a good name is good**: `η₀ + ω^e` good with `ω^e ∣ η₀` gives `η₀` good. -/
theorem ggPrefixE {η0 e : Ordinal.{0}} (hd : ω ^ e ∣ η0) (hg : Bt.Good S (η0 + ω ^ e)) : Bt.Good S η0 := by
  have hex : ∃ y'' ≤ ω ^ e, HCl S (ConjT.Aη S η0) (Pv S η0) (η0 + y'') := by
    by_contra h
    push Not at h
    exact (Nn.nnWPlat h).2 hg
  obtain ⟨y'', hy'', hmem⟩ := hex
  have hH : HCl S (ConjT.Aη S η0) (Pv S η0) η0 := by
    rcases hy''.lt_or_eq with hlt | heq
    · exact Nn.nnHCl_of_add hd hlt hmem
    · rw [heq] at hmem
      have hexp := ggExp_HCl hmem
      rw [cpExp_add η0 (Nn.nn_opow_ne e), ggExp_opow] at hexp
      obtain ⟨q, rfl⟩ := hd
      set k := q % ω with hk
      have hkω : k < ω := mod_lt q omega0_ne_zero
      obtain ⟨n, hn⟩ := lt_omega0.1 hkω
      have hq : q = ω * (q / ω) + k := (div_add_mod q ω).symm
      have hU : ω ^ (e + 1) ≠ 0 := Nn.nn_opow_ne _
      have hsmall : ω ^ e * ((n : Ordinal.{0}) + 1) < ω ^ (e + 1) := by
        rw [← Nat.cast_succ, ← succ_eq_add_one]; exact gg_opow_mul_lt e (n + 1)
      have he1 : ω ^ e * q + ω ^ e = ω ^ (e + 1) * (q / ω) + ω ^ e * ((n : Ordinal.{0}) + 1) := by
        conv_lhs => rw [hq, hn]
        rw [mul_add, add_assoc, ← mul_add_one, opow_add, opow_one, mul_assoc]
      have hpre := Nn.nnHCl_pre (e + 1) hmem
      rw [he1, Nn.nn_div_eq hU hsmall] at hpre
      have e2 : ω ^ e * q = ω ^ (e + 1) * (q / ω) + ω ^ e * (n : Ordinal.{0}) := by
        conv_lhs => rw [hq, hn]
        rw [mul_add, opow_add, opow_one, mul_assoc]
      have h3 := HCl.add hpre (ggHCl_mul_nat hexp.opow n)
      rwa [← e2] at h3
  exact (hH.mono le_self_add).mem_CSet

/-- **The index of a limit `L` with `ζ + Ω₁ ≤ L` for all `ζ < L` is a fixed point of `υ`.** -/
theorem ggFix {L : Ordinal.{0}} (hL : IsSuccLimit L) (hgap : ∀ ζ < L, ζ + Om 1 ≤ L) :
    upsilon (iota S L) = iota S L := by
  set i := iota S L with hi
  have hne : ({ζ | iota S ζ = i} : Set Ordinal.{0}).Nonempty := ⟨L, rfl⟩
  set ζs := sInf {ζ | iota S ζ = i} with hζs
  have hs : iota S ζs = i := csInf_mem hne
  have hsL : ζs ≤ L := csInf_le' (show L ∈ {ζ | iota S ζ = i} from rfl)
  have hmin : ∀ ζ < ζs, iota S ζ < i := fun ζ h =>
    lt_of_le_of_ne (hs ▸ iota_mono _ _ h.le) (fun e => notMem_of_lt_csInf' h e)
  have hone : ∀ ζ, 1 ≤ iota S ζ := fun ζ => by
    have := iota_mono (S := S) ζ 0 zero_le; rwa [iota_zero] at this
  -- every index below `i` has its `υ`-value at most `i`
  have key : ∀ ζ, iota S ζ < i → upsilon (iota S ζ) ≤ i := by
    intro ζ hζ
    obtain ⟨hg, hι, hlt⟩ := cdEta_spec (S := S) (hone ζ) hζ
    set η' := cdEta S (iota S ζ) with hη'
    have hP : Pv S η' = upsilon (iota S ζ) := by
      rw [← hι]; exact (ups_iota S η').symm
    have h2 : iota S (η' + Pv S η') = iota S ζ + Pv S η' := by
      rw [Rz.rz_iota_shift hg le_rfl, hι]
    have h3 : η' + Pv S η' ≤ L :=
      ((add_lt_add_iff_left _).2 (Pv_lt_Om1 S η')).le.trans (hgap _ hlt)
    calc upsilon (iota S ζ) = Pv S η' := hP.symm
      _ ≤ iota S ζ + Pv S η' := le_add_self
      _ = iota S (η' + Pv S η') := h2.symm
      _ ≤ i := iota_mono L _ h3
  -- the least `ζ` with `ι(ζ) = i` is a limit
  have hlim : IsSuccLimit ζs := by
    rcases zero_or_succ_or_isSuccLimit ζs with h0 | ⟨β, hβ⟩ | hl
    · exfalso
      rw [h0, iota_zero] at hs
      have h1 := iota_mono (S := S) L 1 (Order.one_le_iff_pos.2 hL.bot_lt)
      have e1 : iota S (0 + 1) = iota S 0 + 1 := iota_good (Nm.good_zero S)
      rw [zero_add, iota_zero] at e1
      rw [e1, ← hi, ← hs] at h1
      exact absurd h1 (not_le.2 (lt_add_one 1))
    · exfalso
      have hβlt : β < ζs := by rw [← hβ]; exact lt_succ β
      have hgβ : Bt.Good S β := by
        by_contra hb
        have := iota_bad (S := S) hb
        rw [← succ_eq_add_one, hβ, hs] at this
        exact (hmin β hβlt).ne this.symm
      have hg1 : Bt.Good S (β + 1) := good_add hgβ (CSet.one_mem _ _)
      have hζL : ζs < L := lt_of_le_of_ne hsL fun e => by
        rw [← e, ← hβ] at hL; exact not_isSuccLimit_succ β hL
      have hβ' : β + 1 = ζs := by rw [← succ_eq_add_one]; exact hβ
      have h2 := iota_good (S := S) hg1
      rw [hβ', hs] at h2
      have h3 := iota_mono (S := S) L (ζs + 1) (by rw [← succ_eq_add_one]; exact (hL.succ_lt hζL).le)
      rw [h2, ← hi] at h3
      exact absurd h3 (not_le.2 (lt_add_one i))
    · exact hl
  haveI : Nonempty (Iio ζs) := ⟨⟨0, hlim.bot_lt⟩⟩
  have hi' : i = ⨆ e : Iio ζs, iota S e.1 := by rw [← hs, iota_limit hlim]
  refine le_antisymm ?_ upsilon_normal.strictMono.le_apply
  have e1 : upsilon i = ⨆ e : Iio ζs, upsilon (iota S e.1) := by
    rw [hi']; exact upsilon_normal.map_iSup (iota_bdd ζs)
  rw [e1]
  exact ciSup_le' fun e => key e.1 (hmin e.1 e.2)

/-- **THE COFINAL NAMES**: at a named fixed point `F` of `υ` and a code `c` over `Z < F` with `Ω₁ ≤ c < e(η_F)`,
every `ν < F` has a fixed point `μ = ι(η₁ + ω^c)` of `υ` with `ν < μ < F`, `Z ≤ μ` and `e(η_μ) = c`. -/
theorem ggCof {F ηx c Z ν : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hc : GgCl Z c) (hc1 : Om 1 ≤ c) (hce : c < cdExp (cdEta S F))
    (hZ : Z < F) (hν : ν < F) :
    ∃ μ, IsRestartIdx μ ∧ upsilon μ = μ ∧ ν < μ ∧ μ < F ∧ Z ≤ μ ∧ cdExp (cdEta S μ) = c := by
  obtain ⟨hg, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hFlim : IsSuccLimit F := ri_lim hF
  have hww := (cp_fix_facts hF hfix).2.2
  have hη0 : cdEta S F ≠ 0 := by
    intro h
    rw [h, iota_zero] at hι
    have h1 : (1 : Ordinal.{0}) < ω * ω := lt_of_lt_of_le one_lt_omega0 (le_mul_left _ omega0_pos)
    exact absurd (hι ▸ hww) (not_lt.2 h1.le)
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp hη0
  set e := cdExp (cdEta S F) with he
  set i1 := max ν Z + 1 with hi1
  have hi1F : i1 < F := by
    rw [hi1, ← succ_eq_add_one]; exact hFlim.succ_lt (max_lt hν hZ)
  have h1i1 : 1 ≤ i1 := by rw [hi1]; exact le_add_self
  obtain ⟨hg1, hι1, hlt1⟩ := cdEta_spec (S := S) h1i1 (by rw [hι]; exact hi1F)
  set η1 := cdEta S i1 with hη1
  have hce' : ω ^ c < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 hce
  -- `η₁ + ω^c < η_F`
  have hlt' : η1 + ω ^ c < cdEta S F := by
    rw [hdec]
    rcases lt_or_ge η1 η0 with h | h
    · calc η1 + ω ^ c ≤ η0 + ω ^ c := by gcongr
        _ < η0 + ω ^ e := (add_lt_add_iff_left _).2 hce'
    · obtain ⟨t, ht1⟩ := exists_add_of_le h
      have ht : t < ω ^ e := by
        have := hlt1; rw [hdec, ht1] at this; exact (add_lt_add_iff_left _).1 this
      rw [ht1, add_assoc]
      exact (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e ht hce')
  -- `η₁ + ω^c` is good
  have hP1 : Pv S η1 = upsilon i1 := by rw [← hι1]; exact (ups_iota S η1).symm
  have hZP : Z ≤ Pv S (η1 + ω ^ c) := by
    calc Z ≤ max ν Z := le_max_right _ _
      _ ≤ i1 := le_self_add
      _ ≤ upsilon i1 := upsilon_normal.strictMono.le_apply
      _ = Pv S η1 := hP1.symm
      _ ≤ Pv S (η1 + ω ^ c) := Pv_mono le_self_add
  have hg' : Bt.Good S (η1 + ω ^ c) := by
    refine good_add hg1 ?_
    have hcC : c ∈ S.CSet (ConjT.Aη S (η1 + ω ^ c) + 1) (Pv S (η1 + ω ^ c)) := hc.mem_CSet hZP
    have := CSet.phi_mem (CSet.zero_mem _ _) hcC
    rwa [veblen_zero_apply] at this
  -- `ι(η₁ + ω^c)` is a fixed point of `υ`
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans one_lt_Om1) hc1).ne'
  have hOm : Om 1 ≤ ω ^ c := by
    rw [← Om1_opow]; exact opow_le_opow_right omega0_pos hc1
  have hp1 : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
    rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
  have hgap : ∀ ζ < η1 + ω ^ c, ζ + Om 1 ≤ η1 + ω ^ c := by
    intro ζ hζ
    rcases lt_or_ge ζ η1 with h | h
    · calc ζ + Om 1 ≤ η1 + Om 1 := by gcongr
        _ ≤ η1 + ω ^ c := (add_le_add_iff_left _).2 hOm
    · obtain ⟨s, rfl⟩ := exists_add_of_le h
      have hs : s < ω ^ c := (add_lt_add_iff_left _).1 hζ
      rw [add_assoc]
      refine (add_le_add_iff_left _).2 ?_
      rcases hOm.lt_or_eq with hlt | heq
      · exact (isPrincipal_add_omega0_opow c hs hlt).le
      · rw [← heq] at hs ⊢; exact (hp1.add_eq_right hs).le
  have hfx := ggFix (S := S) (isSuccLimit_add η1 (gg_opow_lim hc0)) hgap
  set μ := iota S (η1 + ω ^ c) with hμ
  have hμ1 : 1 ≤ μ := by have := iota_mono (S := S) (η1 + ω ^ c) 0 zero_le; rwa [iota_zero] at this
  have hμ0 : μ ≠ 0 := (lt_of_lt_of_le zero_lt_one hμ1).ne'
  have hi1μ : i1 < μ := by
    rw [← hι1]; exact cd_iota_lt_of_good hg1 (lt_add_of_pos_right _ (opow_pos _ omega0_pos))
  refine ⟨μ, Fx.fx_ri_of_fix hμ0 hfx, hfx, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left ν Z).trans_lt ((lt_add_one _).trans hi1μ)
  · rw [← hι]; exact cd_iota_lt_of_good hg' hlt'
  · exact ((le_max_right ν Z).trans_lt ((lt_add_one _).trans hi1μ)).le
  · rw [cdEta_unique hg' rfl, cpExp_add η1 (Nn.nn_opow_ne c), ggExp_opow]

/-- **The window**: with `η_F = η₀ + ω^{e(η_F)}`, `ι(η₀) < F`, and every restart `μ` with `ι(η₀) < μ < F` has
`e(η_μ) < e(η_F)`. -/
theorem ggWin {F ηx η0 : Ordinal.{0}} (hF : IsRestartIdx F) (hX : upsilon F < Pv S ηx)
    (hdec : cdEta S F = η0 + ω ^ cdExp (cdEta S F)) (hd : ω ^ cdExp (cdEta S F) ∣ η0) :
    iota S η0 < F ∧ ∀ μ, IsRestartIdx μ → iota S η0 < μ → μ < F →
      cdExp (cdEta S μ) < cdExp (cdEta S F) := by
  obtain ⟨hg, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hg0 : Bt.Good S η0 := ggPrefixE hd (hdec ▸ hg)
  have hlt0 : η0 < cdEta S F := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  refine ⟨by rw [← hι]; exact cd_iota_lt_of_good hg0 hlt0, fun μ hμ h1 h2 => ?_⟩
  have hXμ : upsilon μ < Pv S ηx := (upsilon_normal.strictMono h2).trans hX
  obtain ⟨hgμ, hιμ, -, -⟩ := cdEta_pv_spec (S := S) hμ.1 hXμ
  have a1 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have := iota_mono (S := S) η0 _ h
    rw [hιμ] at this
    exact absurd h1 (not_lt.2 this)
  have a2 : cdEta S μ < η0 + ω ^ cdExp (cdEta S F) := by
    rw [← hdec]
    by_contra h
    push Not at h
    have := iota_mono (S := S) _ _ h
    rw [hιμ, hι] at this
    exact absurd h2 (not_lt.2 this)
  exact (cdWin hd a1 a2).1

end Googology.Trans.PoR.InaccPsi.R2.Gg
