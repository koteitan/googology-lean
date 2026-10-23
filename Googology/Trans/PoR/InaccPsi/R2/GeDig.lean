import Googology.Trans.PoR.InaccPsi.R2.GeTow

/-!
# The digits of sums and powers of codes: the codes over a closed base `Z` have their digits below `Z`

For the codes `a < Ω₁^ω` of `R2.GeSub` (digits `cᵢ < Ω₁`, gate = the largest digit):

* `gate_lt_Om1` (every digit is below `Ω₁`), `gate_add` (**the digits of `a + b` are digits of `a`, of `b`, or sums of
  two digits**: below every additively closed `Z`), `gate_opow` (**`ω^y < Ω₁^ω` has the single digit `ω^d`**, `y =
  Ω₁·k + d`), `eps_lt_W` (**an `ε`-number below `Ω₁^ω` is at most `Ω₁`**);
* `geCode_gate` (**a code over `Z` below `Ω₁^ω`, with every atom above `Ω₁^ω`, has its gate below `Z`**, for `Z ≤ Ω₁`
  closed under `+` and `φ`);
* `ge_count` (**the codes below `a` with digits below `y < Ω₁` are countably many**: the reading at `y` is injective).

No new axiom.  New definition: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

theorem geW_eq : geW = ω ^ (Om1 * ω) := by
  unfold geW
  conv_lhs => rw [← show ω ^ Om1 = Om1 from Rj.rj_Om1_inE]
  rw [← opow_mul]

theorem gtN_lt_Om1 : ∀ (n : ℕ) (a : Ordinal.{0}), a < oP n → gtN n a < Om1
  | 0, _, _ => Ordinal.omega_pos 1
  | n + 1, a, ha => max_lt (dm_lt ha) (gtN_lt_Om1 n _ (Ordinal.mod_lt a (oP_ne n)))

/-- **Every digit is below `Ω₁`.** -/
theorem gate_lt_Om1 {a : Ordinal.{0}} (ha : a < geW) : gate a < Om1 := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  rw [(sbc_eq hn 0).2]; exact gtN_lt_Om1 n a hn

theorem oP_absorb (n : ℕ) {r q : Ordinal.{0}} (hr : r < oP n) (hq : q ≠ 0) : r + oP n * q = oP n * q := by
  rw [oP_eq] at hr ⊢
  exact add_of_omega0_opow_le hr (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq))

/-- **The digits of a sum**, level by level. -/
theorem gtN_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) : ∀ (n : ℕ) (a b : Ordinal.{0}),
    a < oP n → b < oP n → gtN n a < Z → gtN n b < Z → gtN n (a + b) < Z
  | 0, a, b, _, _, ha, _ => by rw [show gtN 0 (a + b) = 0 from rfl]; exact (show gtN 0 a = 0 from rfl) ▸ ha
  | n + 1, a, b, ha, hb, hga, hgb => by
      simp only [gtN, max_lt_iff] at hga hgb
      set qa := a / oP n
      set ra := a % oP n
      set qb := b / oP n
      set rb := b % oP n
      have hra : ra < oP n := Ordinal.mod_lt a (oP_ne n)
      have hrb : rb < oP n := Ordinal.mod_lt b (oP_ne n)
      have ea : a = oP n * qa + ra := (Ordinal.div_add_mod a (oP n)).symm
      have eb : b = oP n * qb + rb := (Ordinal.div_add_mod b (oP n)).symm
      show max ((a + b) / oP n) (gtN n ((a + b) % oP n)) < Z
      rcases eq_or_ne qb 0 with hq0 | hq0
      · have e : a + b = oP n * qa + (ra + rb) := by
          rw [ea, eb, hq0, mul_zero, zero_add, add_assoc]
        have hs : ra + rb < oP n := (oP_indec n).add_lt hra hrb
        obtain ⟨d1, d2⟩ := dm_eq (n := n) (q := qa) hs
        rw [e, d1, d2]
        exact max_lt hga.1 (gtN_add hZ n ra rb hra hrb hga.2 hgb.2)
      · have e : a + b = oP n * (qa + qb) + rb := by
          rw [ea, eb, add_assoc, ← add_assoc ra, oP_absorb n hra hq0, ← add_assoc, ← mul_add]
        obtain ⟨d1, d2⟩ := dm_eq (n := n) (q := qa + qb) hrb
        rw [e, d1, d2]
        exact max_lt (hZ _ _ hga.1 hgb.1) hgb.2

/-- **The digits of a sum of codes** lie below every additively closed `Z`. -/
theorem gate_add {Z a b : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (ha : a < geW) (hb : b < geW)
    (hga : gate a < Z) (hgb : gate b < Z) : a + b < geW ∧ gate (a + b) < Z := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  obtain ⟨m, hm⟩ := lt_W_iff.1 hb
  have hn' : a < oP (max n m) := hn.trans_le (oP_mono (le_max_left _ _))
  have hm' : b < oP (max n m) := hm.trans_le (oP_mono (le_max_right _ _))
  have hs : a + b < oP (max n m) := (oP_indec _).add_lt hn' hm'
  refine ⟨lt_W_iff.2 ⟨_, hs⟩, ?_⟩
  rw [(sbc_eq hn' 0).2] at hga
  rw [(sbc_eq hm' 0).2] at hgb
  rw [(sbc_eq hs 0).2]
  exact gtN_add hZ _ a b hn' hm' hga hgb

/-- **A power `ω^y < Ω₁^ω`**: `y = Ω₁·k + d`, `ω^y = Ω₁^k · ω^d` has the single digit `ω^d`. -/
theorem gate_opow {Z y : Ordinal.{0}} (hZ : ∀ u, u < Z → ω ^ u < Z) (hZ0 : 0 < Z) (hy : y < geW) (hgy : gate y < Z)
    (hw : ω ^ y < geW) : gate (ω ^ y) < Z := by
  rw [geW_eq] at hw
  have hyk : y < Om1 * ω := (opow_lt_opow_iff_right one_lt_omega0).1 hw
  set k := y / Om1
  set d := y % Om1
  have hk : k < ω := (Ordinal.div_lt Om1_ne).2 hyk
  obtain ⟨j, hj⟩ := lt_omega0.1 hk
  have hd1 : d < Om1 := Ordinal.mod_lt y Om1_ne
  have ey : y = Om1 * k + d := (Ordinal.div_add_mod y Om1).symm
  have hy2 : y < oP 2 := by
    unfold oP
    rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, opow_add, opow_one]
    exact hyk.trans ((mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).2 (omega0_lt_inE Rj.rj_Om1_inE))
  have hdZ : d < Z := by
    rw [(sbc_eq hy2 0).2] at hgy
    have h1 : oP 1 = Om1 := by unfold oP; simp
    have : gtN 2 y = max (y / oP 1) (gtN 1 (y % oP 1)) := rfl
    rw [this, h1, (sbN_one _ 0).2] at hgy
    exact (le_max_right _ _).trans_lt hgy
  have ew : ω ^ y = oP j * ω ^ d := by rw [ey, hj, opow_add, ← oP_eq]
  have hwd : ω ^ d < Om1 := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hd1
    rwa [show ω ^ Om1 = Om1 from Rj.rj_Om1_inE] at this
  have hlev : ω ^ y < oP (j + 1) := by
    rw [ew, oP_succ]
    exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 (oP_ne j))).2 hwd
  rw [(sbc_eq hlev 0).2]
  show max ((ω ^ y) / oP j) (gtN j ((ω ^ y) % oP j)) < Z
  have e2 : ω ^ y = oP j * ω ^ d + 0 := by rw [add_zero]; exact ew
  obtain ⟨d1, d2⟩ := dm_eq (n := j) (q := ω ^ d) (pos_iff_ne_zero.2 (oP_ne j))
  rw [e2, d1, d2, gtN_zero_code]
  exact max_lt (hZ d hdZ) hZ0

/-- **An `ε`-number below `Ω₁^ω` is at most `Ω₁`.** -/
theorem eps_lt_W {e : Ordinal.{0}} (he : ω ^ e = e) (hW : e < geW) : e ≤ Om1 := by
  by_contra hlt
  push Not at hlt
  rw [geW_eq] at hW
  have hek : e < Om1 * ω := by
    rw [← he] at hW; exact (opow_lt_opow_iff_right one_lt_omega0).1 hW
  have h1 : Om1 + 1 ≤ e := Order.add_one_le_of_lt hlt
  have h2 : ω ^ (Om1 + 1) ≤ ω ^ e := opow_le_opow_right omega0_pos h1
  rw [he, opow_add, opow_one, show ω ^ Om1 = Om1 from Rj.rj_Om1_inE] at h2
  exact absurd (hek.trans_le h2) (lt_irrefl _)

/-- **A code over `Z` below `Ω₁^ω`, all of whose atoms lie above `Ω₁^ω`, has its gate below `Z`** (`Z ≤ Ω₁`, closed
under `+` and `φ`). -/
theorem geCode_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, geW < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < geW → gate c < Z := by
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hconst : ∀ x, x < Om1 → gate x = x := fun x hx => (sb_const hx 0).2
  induction hc with
  | @small x h => intro _; rw [hconst x (h.trans_le hZ1)]; exact h
  | om => intro _; rw [← Br.Om1_eq, (sb_Om1 0).2]; exact h1Z
  | @atom s hs => intro h; exact absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y _ _ ihx ihy =>
    intro h
    have hx : x < geW := lt_of_le_of_lt le_self_add h
    have hy : y < geW := lt_of_le_of_lt le_add_self h
    exact (gate_add hZa hx hy (ihx hx) (ihy hy)).2
  | @phi x y hx hy ihx ihy =>
    intro h
    have hyW : y < geW := lt_of_le_of_lt (right_le_veblen x y) h
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      exact gate_opow hZw hZ0 hyW (ihy hyW) h
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have hle := eps_lt_W hE h
      rcases hle.lt_or_eq with hlt | heq
      · have hxO : x < Om1 := (left_le_veblen x y).trans_lt hlt
        have hyO : y < Om1 := (right_le_veblen x y).trans_lt hlt
        have hxZ : x < Z := by rw [← hconst x hxO]; exact ihx (hxO.trans Om1_lt_W)
        have hyZ : y < Z := by rw [← hconst y hyO]; exact ihy (hyO.trans Om1_lt_W)
        rw [hconst _ hlt]
        exact hZp x y hxZ hyZ
      · rw [heq, (sb_Om1 0).2]; exact h1Z

/-- **The codes below `a` with digits below `y < Ω₁` are countably many.** -/
theorem ge_count {a y : Ordinal.{0}} (ha : a < geW) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio a // gate b.1 < y} := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  have hyn : y ^ (n : Ordinal.{0}) < Om (1 : Ordinal.{0}) := by
    rw [← Br.Om1_eq]; exact (pw_lt_eN hy n).trans (eN_lt_Om1' hy hy1)
  haveI := Gc.gc_countable hyn
  let f : {b : Iio a // gate b.1 < y} → Iio (y ^ (n : Ordinal.{0})) := fun b =>
    ⟨sbN n b.1.1 y, by
      have hb := b.1.2.trans hn
      have hg : gtN n b.1.1 < y := by rw [← (sbc_eq hb 0).2]; exact b.2
      exact sbN_lt hy.pos n _ hg⟩
  refine Function.Injective.countable (f := f) fun b c hbc => ?_
  have hb := b.1.2.trans hn
  have hc := c.1.2.trans hn
  have hgb : gtN n b.1.1 < y := by rw [← (sbc_eq hb 0).2]; exact b.2
  have hgc : gtN n c.1.1 < y := by rw [← (sbc_eq hc 0).2]; exact c.2
  have e : sbN n b.1.1 y = sbN n c.1.1 y := congrArg Subtype.val hbc
  rcases lt_trichotomy b.1.1 c.1.1 with h | h | h
  · exact absurd e (sbN_lt_mono hy.pos n _ _ h hc hgb hgc).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (sbN_lt_mono hy.pos n _ _ h hb hgc hgb).ne'

end Googology.Trans.PoR.InaccPsi.R2.Ge
