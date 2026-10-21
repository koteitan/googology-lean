import Googology.Trans.PoR.InaccPsi.R2.LgLim

/-!
# The exact place of `λ∞ = sup_n Λ⁺(lvgSys n)`: `λ∞ = ι(Γ_{Ω₁+1})`, and its `ρ` below `L(0)`

`gc 0 = φ(1, Ω₁+1)`, `gc (n+1) = φ(gc n, 0)` are the top codes of `lvgSys n` (`R2.LvGPh`), `ggGam = Γ_{Ω₁+1}` the least
strongly critical ordinal above `Ω₁`.

* `lg_gc_sup` (**`sup_n gc n = Γ_{Ω₁+1}`**), `lg_lt_gc`;
* `lg_ggTh_Gam` (**`Θ_y(Γ_{Ω₁+1}) = lgG(y)`** for strongly critical `y < Ω₁`: the top of `lgUSys` is the reading of
  `Γ_{Ω₁+1}`), `lgUPoly` (**`GgPoly lgUSys Γ_{Ω₁+1}`**: a term for every code below `Γ_{Ω₁+1}`), `lgUni` (THEOREM UNI
  for `lgUSys` at every named fixed point with `e(η_F) ≤ Γ_{Ω₁+1}`);
* `lgLam_loc` (**`λ∞ = ι(Γ_{Ω₁+1})`**), `lgLam_ups` (**`ρ_{λ∞} = P(Γ_{Ω₁+1})`**), `lgLam_lt_L0` (**`P(Γ_{Ω₁+1}) <
  L(0)`**), `lg_fr_order` (`ρ(Λ⁺(lvgSys n)) < ρ(λ∞) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, `λ∞ < L(ω+1)`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph

theorem lg_gc_mono {m n : ℕ} (h : m ≤ n) : gc m ≤ gc n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (left_le_veblen _ _)

/-- **`sup_n gc n = Γ_{Ω₁+1}`.** -/
theorem lg_gc_sup : ⨆ n : ℕ, gc n = ggGam := by
  refine le_antisymm (Ordinal.iSup_le fun n => (gc_lt_Gam n).le) (ggGam_le ⟨?_, ?_⟩ ?_)
  · exact lt_of_lt_of_le veblen_pos (Ordinal.le_iSup (fun n : ℕ => gc n) 0)
  · intro a ha b hb
    obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.1 ha
    obtain ⟨m, hm⟩ := Ordinal.lt_iSup_iff.1 hb
    have hak : a < gc (max n m) := hn.trans_le (lg_gc_mono (le_max_left n m))
    have hbk : b < gc (max n m) := hm.trans_le (lg_gc_mono (le_max_right n m))
    have h1 : veblen a b < veblen (gc (max n m)) 0 :=
      veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hak, hbk.trans_le (left_le_veblen _ _)⟩))
    exact h1.trans_le (Ordinal.le_iSup (fun n : ℕ => gc n) (max n m + 1))
  · exact (lt_add_one _).trans_le ((right_le_veblen 1 (Om 1 + 1)).trans (Ordinal.le_iSup (fun n : ℕ => gc n) 0))

theorem lg_lt_gc {e : Ordinal.{0}} (he : e < ggGam) : ∃ n, e < gc n := by
  rw [← lg_gc_sup] at he
  exact Ordinal.lt_iSup_iff.1 he

/-- **`GgPoly lgUSys Γ_{Ω₁+1}`**: every code below `Γ_{Ω₁+1}` has a term of `lgUSys`. -/
theorem lgUPoly : GgPoly lgUSys ggGam := by
  intro Z c hc hcE
  obtain ⟨n, hn⟩ := lg_lt_gc hcE
  obtain ⟨s, hs⟩ := lvgPoly n Z c hc hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

/-- **`Θ_y(Γ_{Ω₁+1}) = lgG(y)`** for a strongly critical `y < Ω₁`. -/
theorem lg_ggTh_Gam {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y ggGam = lgG y := by
  classical
  have hyE : InE y := Low.opow_eq_self_of_SC hy
  have hy1' : y < Om1 := by rw [Br.Om1_eq]; exact hy1
  refine le_antisymm ?_ (lgG_le fun n => ?_)
  · unfold ggTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    by_cases hcC : c.1 ∈ ggSet y
    · rw [if_pos hcC]
      obtain ⟨n, hn⟩ := lg_lt_gc c.2
      refine Order.add_one_le_of_lt ?_
      have h1 : ggTh y c.1 < ggTh y (gc n) := ggTh_lt hcC hn
      rw [gcTh hy hy1 n] at h1
      exact h1.trans (gT_lt_lgG hyE hy1' n)
    · rw [if_neg hcC]; exact zero_le
  · rw [← gcTh hy hy1 n]
    exact (ggTh_lt (gc_cl hy n) (gc_lt_Gam n)).le

variable {S : InaccSeq.{0}}

/-- **THEOREM UNI for `lgUSys`**: `O_U(F) = Θ_F(e(η_F))` at every named fixed point with `e(η_F) ≤ Γ_{Ω₁+1}`. -/
theorem lgUni {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ ggGam) : xtOrec lgUSys F = ggTh F (cdExp (cdEta S F)) :=
  ggUni le_rfl lgUPoly F ηx hF hfix hX he

theorem lg_gc_eps : ∀ n : ℕ, ω ^ gc n = gc n
  | 0 => gg_veblen_eps one_ne_zero
  | n + 1 => gg_veblen_eps (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) (gc_Om1_le n)).ne'

theorem lg_gc_mul_lt (n : ℕ) : gc n * ω < ggGam := by
  have e : gc n * ω = ω ^ (gc n + 1) := by
    rw [opow_add, opow_one, lg_gc_eps n]
  rw [e, ← veblen_zero_apply]
  exact ggGam_spec.1.2 0 ggGam_spec.1.1 _ (ggGam_spec.1.add_one_lt (gc_lt_Gam n))

theorem lg_Gam_lim : IsSuccLimit ggGam := by
  rw [← Low.opow_eq_self_of_SC ggGam_spec.1]
  exact ph_opow_lim ggGam_spec.1.1.ne'

/-- **`λ∞ = ι(Γ_{Ω₁+1})`.** -/
theorem lgLam_loc : lgLam = iota S ggGam := by
  have hB : ∀ n : ℕ, xtB1 (lvgSys (n + 1)) = iota S (gc (n + 1) * ω) := fun n => (lvg_loc (S := S) n).1
  refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
  · have h1 : xtB1 (lvgSys n) ≤ xtB1 (lvgSys (n + 1)) := ((lvg_order n).1.trans (lvg_order n).2.1).le
    calc xtB1 (lvgSys n) ≤ xtB1 (lvgSys (n + 1)) := h1
      _ = iota S (gc (n + 1) * ω) := hB n
      _ ≤ iota S ggGam := iota_mono _ _ (lg_gc_mul_lt (n + 1)).le
  · rw [iota_limit lg_Gam_lim]
    refine ciSup_le' fun e => ?_
    obtain ⟨n, hn⟩ := lg_lt_gc e.2
    have h1 : e.1 ≤ gc (n + 1) * ω :=
      (hn.le.trans (lg_gc_mono (Nat.le_succ n))).trans (le_mul_left _ omega0_pos)
    calc iota S e.1 ≤ iota S (gc (n + 1) * ω) := iota_mono _ _ h1
      _ = xtB1 (lvgSys (n + 1)) := (hB n).symm
      _ ≤ lgLam := (lgB1_lt_lgLam (n + 1)).le

/-- **`ρ_{λ∞} = P(Γ_{Ω₁+1})`.** -/
theorem lgLam_ups : upsilon lgLam = Pv S ggGam := by
  rw [lgLam_loc (S := S), ups_iota S]

theorem lg_Om2_good : Bt.Good S (Om (1 + 1)) :=
  CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))

/-- **`ρ_{λ∞} = P(Γ_{Ω₁+1}) < L(0)`**, and `λ∞ < ι(Ω_ω)`. -/
theorem lgLam_lt_L0 : lgLam < iota S (Om ω) ∧ upsilon lgLam < Nc.ncL S 0 := by
  have h1 : lgLam < iota S (Om ω) := by
    rw [lgLam_loc (S := S)]
    exact (iota_mono _ _ ggGam_le_Om2).trans_lt (cd_iota_lt_of_good lg_Om2_good ph_Om2_lt_Omw)
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  exact ⟨h1, by rw [hL0]; exact upsilon_normal.strictMono h1⟩

/-- **Where `λ∞` lies**: `ρ(Λ⁺(lvgSys n)) < ρ(λ∞) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and `λ∞ < L(ω+1)`,
unconditionally. -/
theorem lg_fr_order (n k : ℕ) :
    upsilon (xtB1 (lvgSys n)) < upsilon lgLam ∧ upsilon lgLam < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    lgLam < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  have hU := (lgLam_lt_L0 (S := S)).2
  refine ⟨upsilon_normal.strictMono (lgB1_lt_lgLam n), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
