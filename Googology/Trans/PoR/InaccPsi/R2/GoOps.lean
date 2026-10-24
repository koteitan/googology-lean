import Googology.Trans.PoR.InaccPsi.R2.GoOp

/-!
# OPERATIONS ON DIGIT SYSTEMS: the step, the `ω`-iterate of an operation, the diagonal of a sequence

An operation `O : GoOp` maps every digit system `D` (`R2.GoD`) to a digit system extending it whose bound is
`φ(1, ix + ω^e)` and whose base is `φ(1, i(x) + ω^e)` (`D.b x = φ(1, i(x))`), for a constant `e < ε₀`; the offset
`ba` grows by a constant `d ∈ [ω^e, ω^{e+1})`.

* `stepOp` (**THE GENERIC HEREDITARY STEP AS AN OPERATION**, `e = 0`);
* `GoOp.U` (**THE UNION OF THE ITERATES `O^k(D)`**, `e ↦ e + 1`, through `GoSeq.toCh` and `GoCh.lim`);
* `GoOpSeq.diag` (**THE DIAGONAL**: the union of `O_k(D)` for a sequence of operations each extending the previous,
  `e = sup_k e_k`);
* `GoExt` (`O'(D)` extends `O(D)`), `GoOp.ext_U`, `GoOpSeq.ext_diag`, `GoOp.F_B`, `GoOp.B_lt`.

No new axiom.  New definitions: `GoOp`, `GoOp.seq`, `GoOp.U`, `stepOp`, `GoExt`, `GoOpSeq`, `GoOpSeq.seq`,
`GoOpSeq.diag`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem go_eps0_E : InE (ε₀ : Ordinal.{0}) := omega0_opow_epsilon 0

theorem go_eps0_lim : IsSuccLimit (ε₀ : Ordinal.{0}) := ev_isSuccLimit_of_inE go_eps0_E

theorem go_opow_lt_eps0 {e : Ordinal.{0}} (he : e < ε₀) : ω ^ e < ε₀ := go_eps0_E.opow_lt he

/-- `d < ω^{e+1} ⇒ d·ω ≤ ω^{e+1}`. -/
theorem go_mul_omega_le {d e : Ordinal.{0}} (hd : d < ω ^ (e + 1)) : d * ω ≤ ω ^ (e + 1) := by
  have hI : ∀ u v, u < ω ^ (e + 1) → v < ω ^ (e + 1) → u + v < ω ^ (e + 1) :=
    fun u v hu hv => isPrincipal_add_omega0_opow _ hu hv
  have hk : ∀ k : ℕ, d * k < ω ^ (e + 1) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, mul_zero]; exact opow_pos _ omega0_pos
    | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact hI _ _ ih hd
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [zero_mul]; exact zero_le
  refine ((isNormal_mul_right (pos_iff_ne_zero.2 hd0)).le_iff_forall_le isSuccLimit_omega0).2 fun b hb => ?_
  obtain ⟨k, rfl⟩ := lt_omega0.1 hb
  exact (hk k).le

/-- `d·k < d·ω` cofinally: `t < d·ω ⇒ t < d·k` for some `k`. -/
theorem go_lt_mul_omega {d t : Ordinal.{0}} (hd : 0 < d) (ht : t < d * ω) : ∃ k : ℕ, t < d * k := by
  obtain ⟨b, hb, htb⟩ := ((isNormal_mul_right hd).lt_iff_exists_lt isSuccLimit_omega0).1 ht
  obtain ⟨k, rfl⟩ := lt_omega0.1 hb
  exact ⟨k, htb⟩

/-- **An operation on digit systems**: base index `+ ω^e`, offset `+ d`, extending. -/
structure GoOp where
  F : GoD → GoD
  e : Ordinal.{0}
  d : Ordinal.{0}
  e_lt : e < ε₀
  e_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → e ∈ S.CSet a b
  d_ge : ω ^ e ≤ d
  d_lt : d < ω ^ (e + 1)
  ix : ∀ D, (F D).ix = D.ix + ω ^ e
  bv : ∀ D x, InE x → x < Om1 → (F D).b x = veblen 1 (evIx (D.b x) + ω ^ e)
  ba : ∀ D x, (F D).ba x = D.ba x + d
  coh_R : ∀ D c x, c < D.B → (F D).R c x = D.R c x
  coh_g : ∀ D c, c < D.B → (F D).g c = D.g c
  cfg : ∀ D, (F D).g D.B < ε₀

namespace GoOp

variable (O : GoOp)

theorem d_pos : 0 < O.d := (opow_pos _ omega0_pos).trans_le O.d_ge

theorem d_lt0 : O.d < ε₀ := O.d_lt.trans (go_opow_lt_eps0 (go_eps0_lim.add_one_lt O.e_lt))

theorem F_B (D : GoD) : (O.F D).B = veblen 1 (D.ix + ω ^ O.e) := by rw [(O.F D).B_ix, O.ix]

theorem B_lt (D : GoD) : D.B < (O.F D).B := by
  rw [O.F_B, D.B_ix]
  exact (isNormal_veblen 1).strictMono (lt_add_of_pos_right _ (opow_pos _ omega0_pos))

theorem it_ix (D : GoD) : ∀ k : ℕ, (O.F^[k] D).ix = D.ix + ω ^ O.e * k
  | 0 => by rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, add_zero]
  | k + 1 => by rw [Function.iterate_succ_apply', O.ix, it_ix D k, Nat.cast_succ, mul_add_one, add_assoc]

theorem it_ba (D : GoD) (x : Ordinal.{0}) : ∀ k : ℕ, (O.F^[k] D).ba x = D.ba x + O.d * k
  | 0 => by rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, add_zero]
  | k + 1 => by rw [Function.iterate_succ_apply', O.ba, it_ba D x k, Nat.cast_succ, mul_add_one, add_assoc]

theorem it_b (D : GoD) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ k : ℕ, (O.F^[k] D).b x = veblen 1 (evIx (D.b x) + ω ^ O.e * k)
  | 0 => by
    rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, add_zero]
    exact (epsilon_evIx (D.b_E x hx hx1)).symm
  | k + 1 => by
    rw [Function.iterate_succ_apply', O.bv _ x hx hx1, it_b D hx hx1 k, go_evIx_veb, Nat.cast_succ, mul_add_one,
      add_assoc]

/-- The sequence of the iterates `O^k(D)`. -/
noncomputable def seq (D : GoD) : GoSeq where
  D := fun k => O.F^[k] D
  ix0 := D.ix
  i := fun x => evIx (D.b x)
  a := D.ba
  δ := fun k => ω ^ O.e * k
  s := fun k => O.d * k
  Δ := ω ^ (O.e + 1)
  T := O.d * ω
  hix := O.it_ix D
  hb := fun k _ hx hx1 => O.it_b D hx hx1 k
  hba := fun k x => O.it_ba D x k
  coh_R := fun k c x hc => by rw [Function.iterate_succ_apply']; exact O.coh_R _ c x hc
  coh_g := fun k c hc => by rw [Function.iterate_succ_apply']; exact O.coh_g _ c hc
  cf_g := fun k => by rw [Function.iterate_succ_apply']; exact O.cfg _
  δ_mono := fun k => (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (by exact_mod_cast Nat.lt_succ_self k)
  δ_lt := fun k => omega0_opow_mul_nat_lt (lt_add_one _) k
  δ_cof := fun t ht => by
    obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (by simp)).1 ht
    exact ⟨n, hn.trans_le (mul_le_mul_right' (opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 hc)) _)⟩
  Δ_lim := ph_opow_lim (by simp)
  Δ_lt := go_opow_lt_eps0 (go_eps0_lim.add_one_lt O.e_lt)
  s_lt := fun k => (mul_lt_mul_iff_right₀ O.d_pos).2 (natCast_lt_omega0 k)
  s_cof := fun _ ht => go_lt_mul_omega O.d_pos ht
  T_lt := go_eps0_E.mul_lt O.d_lt0 (omega0_lt_epsilon 0)
  ix_mem := fun S a b ha => CSet.add_mem (D.ix_mem S a b ha) (go_opow_mem (CSet.succ_mem (O.e_mem S a b ha)))
  ix0_lt := (right_le_veblen 1 D.ix).trans_lt (D.B_ix ▸ D.B_lt1)
  a_lt := D.ba_lt
  a_pi := D.ba_pi

theorem seq_D (D : GoD) (k : ℕ) : (O.seq D).D k = O.F^[k] D := rfl

/-- **THE UNION OF THE ITERATES**: `O^ω(D) = ⋃_k O^k(D)`, base index `+ ω^{e+1}`. -/
noncomputable def U : GoOp where
  F := fun D => (O.seq D).toCh.lim
  e := O.e + 1
  d := O.d * ω + 1
  e_lt := go_eps0_lim.add_one_lt O.e_lt
  e_mem := fun S a b ha => CSet.succ_mem (O.e_mem S a b ha)
  d_ge := by
    rw [opow_add, opow_one]; exact (mul_le_mul_right' O.d_ge ω).trans le_self_add
  d_lt := by
    have h1 := go_mul_omega_le O.d_lt
    have hlt : ω ^ (O.e + 1) < ω ^ (O.e + 1 + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)
    have h2 : (1 : Ordinal.{0}) < ω ^ (O.e + 1 + 1) :=
      one_lt_omega0.trans_le (by
        calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ _ := opow_le_opow_right omega0_pos le_add_self)
    exact isPrincipal_add_omega0_opow _ (h1.trans_lt hlt) h2
  ix := fun _ => rfl
  bv := fun D _ hx hx1 => (O.seq D).toCh_lim_b hx hx1
  ba := fun D x => by rw [(O.seq D).toCh_lim_ba]; exact add_assoc _ _ _
  coh_R := fun D c x hc => (O.seq D).toCh.lim_R (n := 0) hc x
  coh_g := fun D c hc => (O.seq D).toCh.lim_g (n := 0) hc
  cfg := fun D => by
    have h := (O.seq D).toCh.lim_g (n := 1) (c := D.B) (O.B_lt D)
    rw [h]; exact O.cfg D

theorem U_F (D : GoD) : O.U.F D = (O.seq D).toCh.lim := rfl

end GoOp

/-- **THE GENERIC HEREDITARY STEP AS AN OPERATION** (`e = 0`, `d = 1`). -/
noncomputable def stepOp : GoOp where
  F := GoD.step
  e := 0
  d := 1
  e_lt := epsilon_pos 0
  e_mem := fun _ _ _ _ => CSet.zero_mem _ _
  d_ge := by rw [opow_zero]
  d_lt := by rw [zero_add, opow_one]; exact one_lt_omega0
  ix := fun D => by rw [opow_zero]; rfl
  bv := fun D x hx hx1 => by
    rw [opow_zero, D.step_b]; exact go_eN_eq (D.b_E x hx hx1)
  ba := fun _ _ => rfl
  coh_R := fun D _ x hc => D.step_R_low hc x
  coh_g := fun D _ hc => D.step_g_low hc
  cfg := fun D => by rw [D.step_g, D.hG_G]; exact epsilon_pos 0

/-- `O'(D)` extends `O(D)` for every `D` (bounds, readings, gates; the old bound has a gate below `ε₀`). -/
def GoExt (O O' : GoOp) : Prop :=
  ∀ D : GoD, (O.F D).B < (O'.F D).B ∧ (∀ c x, c < (O.F D).B → (O'.F D).R c x = (O.F D).R c x) ∧
    (∀ c, c < (O.F D).B → (O'.F D).g c = (O.F D).g c) ∧ (O'.F D).g (O.F D).B < ε₀

/-- `O^ω` extends `O`. -/
theorem GoOp.ext_U (O : GoOp) : GoExt O O.U := by
  intro D
  have h1 : (O.seq D).D 1 = O.F D := by rw [O.seq_D, Function.iterate_one]
  have h2 : (O.seq D).D 2 = O.F (O.F D) := by
    rw [O.seq_D, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one]
  refine ⟨?_, fun c x hc => ?_, fun c hc => ?_, ?_⟩
  · have := (O.seq D).toCh.B_lt 1; rwa [GoSeq.toCh_D, h1] at this
  · have := (O.seq D).toCh.lim_R (n := 1) (c := c) (by rw [GoSeq.toCh_D, h1]; exact hc) x
    rwa [GoSeq.toCh_D, h1] at this
  · have := (O.seq D).toCh.lim_g (n := 1) (c := c) (by rw [GoSeq.toCh_D, h1]; exact hc)
    rwa [GoSeq.toCh_D, h1] at this
  · have := (O.seq D).toCh.lim_g (n := 2) (c := (O.F D).B) (by rw [GoSeq.toCh_D, h2]; exact O.B_lt _)
    rw [GoSeq.toCh_D, h2] at this
    show (O.seq D).toCh.lim.g (O.F D).B < ε₀
    rw [this]; exact O.cfg _

/-- **A sequence of operations**, each extending the previous, with exponents increasing to `e∞ < ε₀`. -/
structure GoOpSeq where
  O : ℕ → GoOp
  einf : Ordinal.{0}
  ext : ∀ k, GoExt (O k) (O (k + 1))
  e_mono : ∀ k, (O k).e < (O (k + 1)).e
  e_lt : ∀ k, (O k).e < einf
  e_cof : ∀ t, t < einf → ∃ k, t < (O k).e
  einf_lt : einf < ε₀
  einf_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → einf ∈ S.CSet a b

namespace GoOpSeq

variable (P : GoOpSeq)

theorem einf_ne : P.einf ≠ 0 := (lt_of_le_of_lt zero_le (P.e_lt 0)).ne'

/-- The sequence `O_k(D)`. -/
noncomputable def seq (D : GoD) : GoSeq where
  D := fun k => (P.O k).F D
  ix0 := D.ix
  i := fun x => evIx (D.b x)
  a := D.ba
  δ := fun k => ω ^ (P.O k).e
  s := fun k => (P.O k).d
  Δ := ω ^ P.einf
  T := ω ^ P.einf
  hix := fun k => (P.O k).ix D
  hb := fun k x hx hx1 => (P.O k).bv D x hx hx1
  hba := fun k x => (P.O k).ba D x
  coh_R := fun k c x hc => (P.ext k D).2.1 c x hc
  coh_g := fun k c hc => (P.ext k D).2.2.1 c hc
  cf_g := fun k => (P.ext k D).2.2.2
  δ_mono := fun k => (opow_lt_opow_iff_right one_lt_omega0).2 (P.e_mono k)
  δ_lt := fun k => (opow_lt_opow_iff_right one_lt_omega0).2 (P.e_lt k)
  δ_cof := fun t ht => by
    obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow P.einf_ne).1 ht
    obtain ⟨k, hk⟩ := P.e_cof c hc
    exact ⟨k, hn.trans (omega0_opow_mul_nat_lt hk n)⟩
  Δ_lim := ph_opow_lim P.einf_ne
  Δ_lt := go_opow_lt_eps0 P.einf_lt
  s_lt := fun k => (P.O k).d_lt.trans_le (opow_le_opow_right omega0_pos
    (Order.add_one_le_of_lt (P.e_lt k)))
  s_cof := fun t ht => by
    obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow P.einf_ne).1 ht
    obtain ⟨k, hk⟩ := P.e_cof c hc
    exact ⟨k, (hn.trans (omega0_opow_mul_nat_lt hk n)).trans_le (P.O k).d_ge⟩
  T_lt := go_opow_lt_eps0 P.einf_lt
  ix_mem := fun S a b ha => CSet.add_mem (D.ix_mem S a b ha) (go_opow_mem (P.einf_mem S a b ha))
  ix0_lt := (right_le_veblen 1 D.ix).trans_lt (D.B_ix ▸ D.B_lt1)
  a_lt := D.ba_lt
  a_pi := D.ba_pi

theorem seq_D (D : GoD) (k : ℕ) : (P.seq D).D k = (P.O k).F D := rfl

/-- **THE DIAGONAL**: `⋃_k O_k(D)`, base index `+ ω^{e∞}`. -/
noncomputable def diag : GoOp where
  F := fun D => (P.seq D).toCh.lim
  e := P.einf
  d := ω ^ P.einf + 1
  e_lt := P.einf_lt
  e_mem := P.einf_mem
  d_ge := le_self_add
  d_lt := by
    have hlt : ω ^ P.einf < ω ^ (P.einf + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)
    have h2 : (1 : Ordinal.{0}) < ω ^ (P.einf + 1) :=
      one_lt_omega0.trans_le (by
        calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ _ := opow_le_opow_right omega0_pos le_add_self)
    exact isPrincipal_add_omega0_opow _ hlt h2
  ix := fun _ => rfl
  bv := fun D _ hx hx1 => (P.seq D).toCh_lim_b hx hx1
  ba := fun D x => by rw [(P.seq D).toCh_lim_ba]; exact add_assoc _ _ _
  coh_R := fun D c x hc => by
    have h := (P.seq D).toCh.lim_R (n := 0) (c := c) ((P.O 0).B_lt D |> hc.trans) x
    rw [h]; exact (P.O 0).coh_R D c x hc
  coh_g := fun D c hc => by
    have h := (P.seq D).toCh.lim_g (n := 0) (c := c) ((P.O 0).B_lt D |> hc.trans)
    rw [h]; exact (P.O 0).coh_g D c hc
  cfg := fun D => by
    have h := (P.seq D).toCh.lim_g (n := 0) (c := D.B) ((P.O 0).B_lt D)
    rw [h]; exact (P.O 0).cfg D

theorem diag_F (D : GoD) : P.diag.F D = (P.seq D).toCh.lim := rfl

/-- The diagonal extends every member of the sequence. -/
theorem ext_diag (k : ℕ) : GoExt (P.O k) P.diag := by
  intro D
  refine ⟨?_, fun c x hc => (P.seq D).toCh.lim_R (n := k) hc x, fun c hc => (P.seq D).toCh.lim_g (n := k) hc, ?_⟩
  · exact (P.seq D).toCh.B_lt k
  · show (P.seq D).toCh.lim.g ((P.O k).F D).B < ε₀
    rw [(P.seq D).toCh.lim_g (n := k + 1) (c := ((P.O k).F D).B) (P.ext k D).1]
    exact (P.ext k D).2.2.2

end GoOpSeq

end Googology.Trans.PoR.InaccPsi.R2.Go
