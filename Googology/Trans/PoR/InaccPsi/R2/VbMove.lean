import Googology.Trans.PoR.InaccPsi.R2.VbLaw
import Googology.Trans.PoR.InaccPsi.R2.UgB

/-!
# The move of the image under `B_n`, at every level

`B_n = Bc.bcB S n`, `MvD` its domain (`Mv.MvD`), `Θ = gxTh Z At`, `W = rxW Z At`, `κ = Rx.rxL S Z At W` (and `Θ'`,
`W'`, `κ'` for `Z'`, `At'`), `RxE S T` the members over `T`, `T_λ = vbT S λ` the image one level down (`VbDef`).

* `vbNum`, `vbNum_spec`, `vbB_Om` (**`Ω_k ∈ MvD` and `B_n Ω_k = Ω_k`** for every finite `k ≥ 1`), `vbB_mulNat`;
* `vbKg_cnf` (`κ` on a Cantor normal form built from members), `vbKg_eps` (`κ y` an `ε`-number, `y ≥ Ω₁`, makes
  `y` an `ε`-number);
* `vbK_move` (**THE MOVE OF `κ`, ONE STATEMENT FOR EVERY LEVEL**): if every countable member `g < T` (`T ≤ W`
  strongly critical) moves with its code (`g, Θ⁻¹ g ∈ MvD`, `B_n g < W'`, `Θ'⁻¹(B_n g) = B_n(Θ⁻¹ g)`), then every
  member `y` over `T` has `y, κ y ∈ MvD`, `B_n y` a member over `W'` and **`κ'(B_n y) = B_n(κ y)`** (and `B_n` keeps
  the `ε`-numbers `y ≥ Ω₁`); one induction on the measure: leaves, `Ω_j`, atoms `ψ_{Ω_{i+1}}(e)` by `Ug.ugB_psiS`
  (generic in the level), Veblen normal forms by `Mw.mwB_phi`, Cantor normal forms by `Mv.mvB_add`, `Mv.mvB_opow`;
* `vbLeaf_of_codes` (**the leaf hypothesis from the move of the codes `< B`** at two restarts);
* `vbT_move` (**THE MOVE OF THE IMAGE**: at restarts `λ, λ'`, for `x ∈ VbD S λ` whose image is a member over `T`,
  `x, T_λ x ∈ MvD` and **`T_{λ'}(B_n x) = B_n(T_λ x)`**).

No new axiom.  New definition: `vbNum` (the numeral terms).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw

variable {S : InaccSeq.{0}}

/-- The numeral terms: `0`, `1`, `1 + (k+1)`. -/
def vbNum : ℕ → Term
  | 0 => Term.zero
  | 1 => tOne
  | k + 2 => Term.add tOne (vbNum (k + 1))

theorem vbNum_spec : ∀ k : ℕ, Term.NF (vbNum k) ∧ bcFree (vbNum k) ∧ Term.val S (vbNum k) = k ∧
    (1 ≤ k → Term.head (vbNum k) = tOne ∧ vbNum k ≠ Term.zero ∧ (vbNum k).isF = false)
  | 0 => ⟨trivial, trivial, by simp [vbNum, Term.val], fun h => absurd h (by omega)⟩
  | 1 => ⟨NF_tOne, bcFree_tOne, by rw [show vbNum 1 = tOne from rfl, val_tOne, Nat.cast_one],
      fun _ => ⟨rfl, tOne_ne_zero, rfl⟩⟩
  | k + 2 => by
    obtain ⟨hN, hf, hv, h1⟩ := vbNum_spec (k + 1)
    obtain ⟨hh, hne, -⟩ := h1 (by omega)
    refine ⟨⟨NF_tOne, hN, rfl, hne, ?_⟩, ⟨bcFree_tOne, hf⟩, ?_, fun _ => ⟨rfl, by simp [vbNum], rfl⟩⟩
    · rw [hh, Term.cmp_self]; simp
    · show Term.val S tOne + Term.val S (vbNum (k + 1)) = _
      rw [val_tOne, hv]
      have e : ((k + 2 : ℕ) : Ordinal.{0}) = ((1 + (k + 1) : ℕ) : Ordinal.{0}) := by congr 1; omega
      rw [e]; norm_cast

/-- **`Ω_k ∈ MvD` and `B_n Ω_k = Ω_k`** for every finite `k ≥ 1`. -/
theorem vbB_Om {n k : ℕ} (hk : 1 ≤ k) :
    MvD S (Om (k : Ordinal.{0})) ∧ bcB S n (Om (k : Ordinal.{0})) = Om (k : Ordinal.{0}) := by
  obtain ⟨hN, hf, hv, h1⟩ := vbNum_spec (S := S) k
  obtain ⟨-, hne, hF⟩ := h1 hk
  have hD : bcD S (Term.om (vbNum k)) := bcD_free ⟨hN, hne, hF⟩ hf
  have hval : Term.val S (Term.om (vbNum k)) = Om (k : Ordinal.{0}) := by
    show Om (Term.val S (vbNum k)) = _
    rw [hv]
  rw [← hval]
  exact ⟨mvD_of_term hD, by rw [mvB_term hD, bcSig_free (show bcFree (Term.om (vbNum k)) from hf)]⟩

theorem vbD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1

theorem vbDnat (m : ℕ) : MvD S (m : Ordinal.{0}) :=
  mvD_of_lt ((natCast_lt_omega0 m).trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))

theorem vbB_mulNat {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) :
    ∀ m : ℕ, MvD S (x * m) ∧ bcB S n (x * m) = bcB S n x * m
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero]; exact ⟨vbD0, bcB_zero n⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := vbB_mulNat (n := n) hx m
    obtain ⟨h3, h4⟩ := mvB_add (k := n) h1 hx
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h3, by rw [h4, h2]⟩

section Gen

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

include hZ hZ1 hAt

/-- `κ` on a Cantor normal form built from members. -/
theorem vbKg_cnf {yl yr : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hylE : RxE S (rxW Z At) yl)
    (hyrE : RxE S (rxW Z At) yr) (hyl1 : Om 1 ≤ yl) (hyrlt : yr < ω ^ yl) :
    RxE S (rxW Z At) (ω ^ yl * n + yr) ∧
      rxL S Z At (rxW Z At) (ω ^ yl * n + yr) =
        ω ^ rxL S Z At (rxW Z At) yl * n + rxL S Z At (rxW Z At) yr := by
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hoW : ω ^ yl < Om ω := by
    have := vbOmW_SC.2 0 (Om_pos omega0_ne_zero) yl hylE.2.2; rwa [veblen_zero_apply] at this
  have hoC : ω ^ yl ∈ S.CSet (Om ω) (ConjT.th S) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hylE.2.1; rwa [veblen_zero_apply] at this
  have hoE : RxE S (rxW Z At) (ω ^ yl) := ⟨RxN.opow hylE.1, hoC, hoW⟩
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxE S (rxW Z At) y :=
    ⟨RxN.add (RxN.mul_nat hoE.1 n) hyrE.1, CSet.add_mem (ConjT.mul_nat_mem S hoC n) hyrE.2.1,
      vbOmW_SC.isPrincipal (vbMulNat_lt vbOmW_SC.isPrincipal vbOmW_SC.1 hoW n) hyrE.2.2⟩
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  refine ⟨hyE, ?_⟩
  obtain ⟨n', -, hdm', hκy, -⟩ := rxLDecK hZ hZ1 hAt hyE hy1
  have hlogy : log ω y = yl := by
    rw [hydef, log_opow_mul_add one_lt_omega0 hn0 hyrlt, log_eq_zero (natCast_lt_omega0 n), add_zero]
  have hmody : y % ω ^ yl = yr := by
    rw [hydef, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyrlt]
  have hyl0 : ω ^ yl ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hnn : (n' : Ordinal.{0}) = n := by
    rw [hlogy, hmody] at hdm'
    have e1 : y / ω ^ yl = n := by
      rw [hydef, Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    have e2 : y / ω ^ yl = n' := by
      rw [hdm', Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    rw [← e1, ← e2]
  rw [hκy, hlogy, hmody, hnn]

/-- `κ y` an `ε`-number (`y ≥ Ω₁` a member) makes `y` an `ε`-number. -/
theorem vbKg_eps {y : Ordinal.{0}} (hy : RxE S (rxW Z At) y) (h1 : Om 1 ≤ y)
    (hε : ω ^ rxL S Z At (rxW Z At) y = rxL S Z At (rxW Z At) y) : ω ^ y = y := by
  by_contra hne
  obtain ⟨n, -, -, hκ, hlE, hrE, -, hrlt, hopx, -, hor, -⟩ := rxLDecK hZ hZ1 hAt hy h1
  have hlz := hor.resolve_left hne
  set x := rxL S Z At (rxW Z At) y with hxdef
  have hll : rxL S Z At (rxW Z At) (log ω y) < x := rxL_mono hZ hZ1 hAt hlE hy hlz
  have hrx : rxL S Z At (rxW Z At) (y % ω ^ log ω y) < x := rxL_mono hZ hZ1 hAt hrE hy (hrlt.trans_le hopx)
  have hx0 : 0 < x := zero_le.trans_lt hll
  have hP : IsPrincipal (· + ·) x := by rw [← hε]; exact isPrincipal_add_omega0_opow _
  have hopx' : ω ^ rxL S Z At (rxW Z At) (log ω y) < x := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hll
    rwa [hε] at this
  have h5 : ω ^ rxL S Z At (rxW Z At) (log ω y) * n + rxL S Z At (rxW Z At) (y % ω ^ log ω y) < x :=
    hP (vbMulNat_lt hP hx0 hopx' n) hrx
  rw [← hκ] at h5
  exact lt_irrefl _ h5

end Gen

section Move

variable {n : ℕ} {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
  {Z' : Ordinal.{0}} {At' : Set Ordinal.{0}} (hZ' : SC Z') (hZ1' : Z' < Om 1) (hAt' : GxAt At')
  {T : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
  (hleaf : ∀ g, g < T → MvD S g ∧ MvD S (ruInv Z At g) ∧ bcB S n g < rxW Z' At' ∧
    ruInv Z' At' (bcB S n g) = bcB S n (ruInv Z At g))

include hZ hZ1 hAt hZ' hZ1' hAt' hT hTW hleaf

/-- **THE MOVE OF `κ`, ONE STATEMENT FOR EVERY LEVEL.** -/
theorem vbK_move : ∀ y, RxE S T y →
    MvD S y ∧ MvD S (rxL S Z At (rxW Z At) y) ∧ RxE S (rxW Z' At') (bcB S n y) ∧
      rxL S Z' At' (rxW Z' At') (bcB S n y) = bcB S n (rxL S Z At (rxW Z At) y) ∧
      (Om 1 ≤ y → ω ^ y = y → ω ^ bcB S n y = bcB S n y) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hW1' := rxW_le_Om1 (Z := Z') (At := At')
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have h1θ : Om 1 < ConjT.th S := (psiS_bounds (S := S) (Om ω) 1).1
  have h1W : Om 1 < Om ω := Om_lt_Om.2 one_lt_omega0
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  refine rxMs_ind (S := S) (T := T) fun y IH hy => ?_
  have hyW : RxE S (rxW Z At) y := hy.mono hTW
  rcases lt_or_ge y (Om 1) with h1 | h1
  · have hyT : y < T := rxE_lt_T hT hy h1
    obtain ⟨hD, hDi, hBW, hinv⟩ := hleaf y hyT
    have hBW1 : bcB S n y < Om 1 := hBW.trans_le hW1'
    refine ⟨hD, by rw [rxL_lt_Om1 h1]; exact hDi,
      ⟨RxN.small hBW, CSet.of_lt (hBW1.trans h1θ), hBW1.trans h1W⟩, ?_, fun h => absurd h (not_le.2 h1)⟩
    rw [rxL_lt_Om1 hBW1, rxL_lt_Om1 h1]; exact hinv
  by_cases hΩ : ∃ j : ℕ, y = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      have h := Om_le_Om.1 h1
      have h' : ((1 : ℕ) : Ordinal.{0}) ≤ j := by rw [Nat.cast_one]; exact h
      exact_mod_cast h'
    obtain ⟨hD, hB⟩ := vbB_Om (S := S) (n := n) hj
    obtain ⟨hD2, hB2⟩ := vbB_Om (S := S) (n := n) (k := j + 1) (by omega)
    rw [Nat.cast_succ] at hD2 hB2
    have hκ : rxL S Z At (rxW Z At) (Om (j : Ordinal.{0})) = Om ((j : Ordinal.{0}) + 1) := rxL_Om hj
    refine ⟨hD, by rw [hκ]; exact hD2, ?_, ?_, fun _ h => by rw [hB]; exact h⟩
    · rw [hB]; exact ⟨RxN.om (rxN_nat j), rxC_Om_nat _ _ j, Om_lt_Om.2 (natCast_lt_omega0 j)⟩
    · rw [hB, rxL_Om hj, hκ, hB2]
  have hy1 : Om 1 < y := lt_of_le_of_ne h1 (fun e => hΩ ⟨1, by rw [← e, Nat.cast_one]⟩)
  by_cases hS : SC y
  · obtain ⟨i, hi, e, heE, hen, rfl, hst⟩ := rxE_atom hT1 hy hS hy1 hΩ
    obtain ⟨hDe, hDκe, hBeE, hκe, -⟩ := IH e (rxMs_lt_stage (rxE_lt_Lam heE) hst) heE
    have heW : RxE S (rxW Z At) e := heE.mono hTW
    have hi0 : (i : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    obtain ⟨hDy, hBy, hBen⟩ := Ug.ugB_psiS (n := n) hi0 (vbDnat i) hDe hen
    rw [mwB_nat] at hBy hBen
    have hκy := (rxL_psiE hi heW hen).1
    have hκen := rxL_tr hZ hZ1 hAt hi heW heW hen hen
    have hi1 : (i : Ordinal.{0}) + 1 ≠ 0 := by
      rw [← Nat.cast_succ]; exact_mod_cast (show i + 1 ≠ 0 by omega)
    have hDi1 : MvD S ((i : Ordinal.{0}) + 1) := by rw [← Nat.cast_succ]; exact vbDnat (i + 1)
    obtain ⟨hDκy, hBκy, -⟩ := Ug.ugB_psiS (n := n) hi1 hDi1 hDκe hκen
    have hBi1 : bcB S n ((i : Ordinal.{0}) + 1) = (i : Ordinal.{0}) + 1 := by
      rw [← Nat.cast_succ]; exact mwB_nat n (i + 1)
    rw [hBi1] at hBκy
    refine ⟨hDy, by rw [hκy]; exact hDκy, by rw [hBy]; exact rxE_psi hi hBeE hBen, ?_,
      fun _ _ => by rw [hBy]; exact gg_SC_eps (SC_psi (InR_Om_succ _) _)⟩
    rw [hBy, (rxL_psiE hi hBeE hBen).1, hκe, hκy, hBκy]
  by_cases hε : ω ^ y = y
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hy1 hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hy hv hb
    obtain ⟨hDa, hDκa, hBaE, hκa, -⟩ := IH _ (rxMs_lt_val hha ha) haE
    obtain ⟨hDb, hDκb, hBbE, hκb, -⟩ := IH _ (rxMs_lt_val hhb hb) hbE
    have hab : invVeblen₁ y < veblen (invVeblen₁ y) (invVeblen₂ y) := by rw [hv]; exact ha
    have hbb : invVeblen₂ y < veblen (invVeblen₁ y) (invVeblen₂ y) := by rw [hv]; exact hb
    obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) hDa hDb hab hbb
    rw [hv] at hDv hBv
    have hκy := rxL_veb (Z := Z) (At := At) hyW hy1 hε hS
    have hκa_lt := rxL_mono hZ hZ1 hAt (haE.mono hTW) hyW ha
    have hκb_lt := rxL_mono hZ hZ1 hAt (hbE.mono hTW) hyW hb
    rw [hκy] at hκa_lt hκb_lt
    obtain ⟨hDκv, hBκv⟩ := mwB_phi (k := n) hDκa hDκb hκa_lt hκb_lt
    have hBa0 : bcB S n (invVeblen₁ y) ≠ 0 := by
      intro h
      have h' := (mvB_lt_iff (k := n) vbD0 hDa).2 ha0
      rw [bcB_zero, h] at h'
      exact lt_irrefl _ h'
    have hBa_lt : bcB S n (invVeblen₁ y) < bcB S n y := (mvB_lt_iff hDa hDv).2 ha
    have hBb_lt : bcB S n (invVeblen₂ y) < bcB S n y := (mvB_lt_iff hDb hDv).2 hb
    have hBy1 : Om 1 < bcB S n y := by
      have h' := (mvB_lt_iff (k := n) hDO hDv).2 hy1
      rwa [hBO] at h'
    have hBε : ω ^ bcB S n y = bcB S n y := by rw [hBv]; exact gg_veblen_eps hBa0
    have hBS : ¬ SC (bcB S n y) := fun h => h.not_veblen_lt hBa_lt hBb_lt hBv.symm
    have hBE : RxE S (rxW Z' At') (bcB S n y) := by
      rw [hBv]
      exact ⟨RxN.phi hBaE.1 hBbE.1, CSet.phi_mem hBaE.2.1 hBbE.2.1, vbOmW_SC.2 _ hBaE.2.2 _ hBbE.2.2⟩
    obtain ⟨hv', -, -, hb'⟩ := rxVeb hBy1 hBε hBS
    have hpair : invVeblen₁ (bcB S n y) = bcB S n (invVeblen₁ y) ∧
        invVeblen₂ (bcB S n y) = bcB S n (invVeblen₂ y) := by
      have e : veblen (invVeblen₁ (bcB S n y)) (invVeblen₂ (bcB S n y)) =
          veblen (bcB S n (invVeblen₁ y)) (bcB S n (invVeblen₂ y)) := hv'.trans hBv
      rcases veblen_eq_veblen_iff.1 e with ⟨e1, e2⟩ | ⟨-, e2⟩ | ⟨-, e3⟩
      · exact ⟨e1, e2⟩
      · exact absurd (e2.trans hBv.symm) hb'.ne
      · exact absurd (e3.symm.trans hv') hBb_lt.ne
    refine ⟨hDv, by rw [hκy]; exact hDκv, hBE, ?_, fun _ _ => hBε⟩
    rw [rxL_veb (Z := Z') (At := At') hBE hBy1 hBε hBS, hpair.1, hpair.2, hκa, hκb, hκy, hBκv]
  -- the Cantor normal form
  obtain ⟨m, hm1, hdm, hκy, hlE, hrE, -, hrlt, hopy, hℓ1, hor, hlh, hrh, -⟩ := rxLDecK hZ hZ1 hAt hyW h1
  have hly : log ω y < y := hor.resolve_left hε
  have hlT : RxE S T (log ω y) := (rxE_log hy).1
  have hrT : RxE S T (y % ω ^ log ω y) := (rxE_rem hy).1
  have hlh' := (rxE_log hy).2
  have hrh' := (rxE_rem hy).2
  obtain ⟨hDl, hDκl, hBlE, hκl, hεl⟩ := IH _ (rxMs_lt_val hlh' hly) hlT
  obtain ⟨hDr, hDκr, hBrE, hκr, -⟩ := IH _ (rxMs_lt_val hrh' (hrlt.trans_le hopy)) hrT
  have hBo : MvD S (ω ^ log ω y) ∧ bcB S n (ω ^ log ω y) = ω ^ bcB S n (log ω y) := by
    by_cases he : ω ^ log ω y = log ω y
    · rw [he]; exact ⟨hDl, (hεl hℓ1 he).symm⟩
    · exact mvB_opow hDl he
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hBo.1 m
  obtain ⟨hDy, hBy⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hDy hBy
  rw [hBom, hBo.2] at hBy
  have hBrlt : bcB S n (y % ω ^ log ω y) < ω ^ bcB S n (log ω y) := by
    rw [← hBo.2]; exact (mvB_lt_iff hDr hBo.1).2 hrlt
  have hBl1 : Om 1 ≤ bcB S n (log ω y) := by
    rcases hℓ1.lt_or_eq with h | h
    · have h' := (mvB_lt_iff (k := n) hDO hDl).2 h
      rw [hBO] at h'; exact h'.le
    · rw [← h, hBO]
  obtain ⟨hBE, hκ'B⟩ := vbKg_cnf hZ' hZ1' hAt' m hm1 hBlE hBrE hBl1 hBrlt
  have hlW : RxE S (rxW Z At) (log ω y) := hlT.mono hTW
  have hBo' : MvD S (ω ^ rxL S Z At (rxW Z At) (log ω y)) ∧
      bcB S n (ω ^ rxL S Z At (rxW Z At) (log ω y)) = ω ^ bcB S n (rxL S Z At (rxW Z At) (log ω y)) := by
    by_cases he : ω ^ rxL S Z At (rxW Z At) (log ω y) = rxL S Z At (rxW Z At) (log ω y)
    · have hlε : ω ^ log ω y = log ω y := vbKg_eps hZ hZ1 hAt hlW hℓ1 he
      have hBlε := hεl hℓ1 hlε
      have hκBε := rxL_eps hZ' hZ1' hAt' hBlE hBl1 hBlε
      rw [hκl] at hκBε
      rw [he]; exact ⟨hDκl, hκBε.symm⟩
    · exact mvB_opow hDκl he
  obtain ⟨hDom', hBom'⟩ := vbB_mulNat (n := n) hBo'.1 m
  obtain ⟨hDκy, hBκy⟩ := mvB_add (k := n) hDom' hDκr
  rw [← hκy] at hDκy hBκy
  refine ⟨hDy, hDκy, by rw [hBy]; exact hBE, ?_, fun _ h => absurd h hε⟩
  rw [hBy, hκ'B, hBκy, hBom', hBo'.2, hκl, hκr]

end Move

section Rst

variable {n : ℕ} {l l' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx')

include hl hX hl' hX'

/-- **The leaf hypothesis from the move of the codes**: if every code `c < Ω₂` of `λ` whose reading is below `T`
moves (`c, Θ c ∈ MvD`, `B_n c` a code `< Ω₂` of `λ'`, `Θ'(B_n c) = B_n(Θ c)`), the countable members `g < T` move. -/
theorem vbLeaf_of_codes {T : Ordinal.{0}} (hTW : T ≤ vbW S l)
    (hc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Om (1 + 1) → gxTh (upsilon l) (ldAtR S l) c < T →
      MvD S c ∧ MvD S (gxTh (upsilon l) (ldAtR S l) c) ∧ GxCl (upsilon l') (ldAtR S l') (bcB S n c) ∧
      bcB S n c < Om (1 + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (bcB S n c) = bcB S n (gxTh (upsilon l) (ldAtR S l) c)) :
    ∀ g, g < T → MvD S g ∧ MvD S (ruInv (upsilon l) (ldAtR S l) g) ∧ bcB S n g < vbW S l' ∧
      ruInv (upsilon l') (ldAtR S l') (bcB S n g) = bcB S n (ruInv (upsilon l) (ldAtR S l) g) := by
  intro g hg
  have hg2 : g < gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := by
    rw [← vbW_eq hl hX]; exact hg.trans_le hTW
  obtain ⟨hcode, hc2, hΘ⟩ := ruInv_spec hg2
  obtain ⟨hD, hDΘ, hcode', hBc2, hmove⟩ := hc _ hcode hc2 (by rw [hΘ]; exact hg)
  rw [hΘ] at hDΘ hmove
  have hBW : bcB S n g < vbW S l' := by
    rw [vbW_eq hl' hX', ← hmove]; exact gxTh_lt hcode' hBc2
  refine ⟨hDΘ, hD, hBW, ?_⟩
  have hBW2 : bcB S n g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hBW
  obtain ⟨h1, -, h3⟩ := ruInv_spec hBW2
  exact ruCode_inj h1 hcode' (h3.trans hmove.symm)

/-- **THE MOVE OF THE IMAGE**: `T_{λ'}(B_n x) = B_n(T_λ x)` for `x ∈ VbD S λ` whose image is a member over `T`. -/
theorem vbT_move {T : Ordinal.{0}} (hT : SC T) (hTW : T ≤ vbW S l)
    (hleaf : ∀ g, g < T → MvD S g ∧ MvD S (ruInv (upsilon l) (ldAtR S l) g) ∧ bcB S n g < vbW S l' ∧
      ruInv (upsilon l') (ldAtR S l') (bcB S n g) = bcB S n (ruInv (upsilon l) (ldAtR S l) g))
    {x : Ordinal.{0}} (hx : VbD S l x) (hxT : RxE S T (vbT S l x)) :
    MvD S x ∧ MvD S (vbT S l x) ∧ RxE S (vbW S l') (bcB S n (vbT S l x)) ∧
      vbK S l' (bcB S n (vbT S l x)) = bcB S n x ∧ vbT S l' (bcB S n x) = bcB S n (vbT S l x) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  obtain ⟨-, hK⟩ := vbT_eq hl hX hx
  obtain ⟨hD, hDκ, hBE, hmove, -⟩ := vbK_move (Z := upsilon l) (At := ldAtR S l) (Z' := upsilon l')
    (At' := ldAtR S l') hZ hZ1 (ldAt_GxAt _ _) hZ' hZ1' (ldAt_GxAt _ _) hT hTW hleaf _ hxT
  have hK' : rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (vbT S l x) = x := hK
  rw [hK'] at hDκ hmove
  refine ⟨hDκ, hD, hBE, hmove, ?_⟩
  have h := vbT_K hl' hX' hBE
  rwa [show vbK S l' (bcB S n (vbT S l x)) = bcB S n x from hmove] at h

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vb
