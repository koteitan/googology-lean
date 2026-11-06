import Googology.Trans.PoR.InaccPsi.R2.KzTop

/-!
# Kz: THE MOVE OF `κ` AND OF `T_K` UNDER `B_n` (`Vb.vbK_move`, `Vb.vbT_move`, `Xq.xqTMove` below a bound `K`)

`B_n = Bc.bcB S n`, `MvD` its domain, `κ = Rx.rxL S Z At W` (and `κ'` for `Z'`, `At'`), `RxEK S T K` the members over
`T` below `K` (`Kz.KzB`), `T_K = vbTK S λ K`.

* `kzKg_cnf`, `kzKg_eps` (`Vb.vbKg_cnf`, `Vb.vbKg_eps` on `RxEK`);
* `kzK_move` (**THE MOVE OF `κ` BELOW `K`**: the proof of `Vb.vbK_move`, with the new case `y = Ω_ω`,
  `B_n Ω_ω = Ω_ω = κ Ω_ω`, `Wr.wrB_OmW`);
* `vbTK_move` (**THE MOVE OF `T_K`**: `T_{K,λ'}(B_n x) = B_n(T_{K,λ} x)` for `x ∈ D_K` whose image is a member over `T`);
* `kzN_cl` (**a member of `Cl(B, Z)` is normal over `Z`** when `ψ₁(B) < Z ≤ Ω₁`; `Xq.xqN_cl` is `B = Ω_ω`);
* `kzLeaf` (`Xq.xqLeaf` with the bound `B_n x < P′` of the band);
* `kzTE` (**`T_K x` is a member over `Θ(ψ₂ a)`** for `x ∈ D_K ∩ Cl(a, ψ₂ a)`, `a ≤ A`: the arguments of `T_K x` are
  below `A`), `kzTMove` (**THE MOVE OF `T_K`** under the moves of the codes below `ψ₂ a`, `a ≤ A`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

section Gen

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
  {K : Ordinal.{0}} (hKB : KzB S K)

include hZ hZ1 hAt hKB

/-- `κ` on a Cantor normal form built from members below `K`. -/
theorem kzKg_cnf {yl yr : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hylE : RxEK S (rxW Z At) K yl)
    (hyrE : RxEK S (rxW Z At) K yr) (hyl1 : Om 1 ≤ yl) (hyrlt : yr < ω ^ yl) :
    RxEK S (rxW Z At) K (ω ^ yl * n + yr) ∧
      rxL S Z At (rxW Z At) (ω ^ yl * n + yr) =
        ω ^ rxL S Z At (rxW Z At) yl * n + rxL S Z At (rxW Z At) yr := by
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxEK S (rxW Z At) K y := kzE_add hKB (kzE_mulNat hKB (kzE_opow hKB hylE) n) hyrE
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  refine ⟨hyE, ?_⟩
  obtain ⟨n', -, hdm', hκy, -⟩ := kzLDecK hZ hZ1 hAt hKB hyE hy1
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

/-- `κ y` an `ε`-number (`y ≥ Ω₁` a member below `K`) makes `y` an `ε`-number. -/
theorem kzKg_eps {y : Ordinal.{0}} (hy : RxEK S (rxW Z At) K y) (h1 : Om 1 ≤ y)
    (hε : ω ^ rxL S Z At (rxW Z At) y = rxL S Z At (rxW Z At) y) : ω ^ y = y := by
  by_contra hne
  obtain ⟨n, -, -, hκ, hlE, hrE, -, hrlt, hopx, -, hor, -⟩ := kzLDecK hZ hZ1 hAt hKB hy h1
  have hlz := hor.resolve_left hne
  set x := rxL S Z At (rxW Z At) y with hxdef
  have hll : rxL S Z At (rxW Z At) (log ω y) < x := kzL_mono hZ hZ1 hAt hKB hlE hy hlz
  have hrx : rxL S Z At (rxW Z At) (y % ω ^ log ω y) < x :=
    kzL_mono hZ hZ1 hAt hKB hrE hy (hrlt.trans_le hopx)
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
  {K : Ordinal.{0}} (hKB : KzB S K)
  {T : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
  (hleaf : ∀ g, g < T → MvD S g ∧ MvD S (ruInv Z At g) ∧ bcB S n g < rxW Z' At' ∧
    ruInv Z' At' (bcB S n g) = bcB S n (ruInv Z At g))

include hZ hZ1 hAt hZ' hZ1' hAt' hKB hT hTW hleaf

/-- **THE MOVE OF `κ` BELOW `K`.** -/
theorem kzK_move : ∀ y, RxEK S T K y →
    MvD S y ∧ MvD S (rxL S Z At (rxW Z At) y) ∧ RxEK S (rxW Z' At') K (bcB S n y) ∧
      rxL S Z' At' (rxW Z' At') (bcB S n y) = bcB S n (rxL S Z At (rxW Z At) y) ∧
      (Om 1 ≤ y → ω ^ y = y → ω ^ bcB S n y = bcB S n y) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hW1' := rxW_le_Om1 (Z := Z') (At := At')
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have h1W : Om 1 < Om ω := Om_lt_Om.2 one_lt_omega0
  have h1K : Om 1 < K := h1W.trans_le hKB.ge
  have h1ψ : Om 1 < S.psi K (Om (1 + 1)) := (psiS_bounds (S := S) K 1).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  refine rxMs_ind (S := S) (T := T) fun y IH hy => ?_
  have hyW : RxEK S (rxW Z At) K y := ⟨hy.1.mono hTW, hy.2⟩
  rcases lt_or_ge y (Om 1) with h1 | h1
  · have hyT : y < T := rxNs_lt_T hT (rxH_spec hy.1) h1
    obtain ⟨hD, hDi, hBW, hinv⟩ := hleaf y hyT
    have hBW1 : bcB S n y < Om 1 := hBW.trans_le hW1'
    refine ⟨hD, by rw [rxL_lt_Om1 h1]; exact hDi,
      ⟨RxN.small hBW, CSet.of_lt (hBW1.trans h1ψ), hBW1.trans h1K⟩, ?_, fun h => absurd h (not_le.2 h1)⟩
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
    · rw [hB]
      exact ⟨RxN.om (rxN_nat j), rxC_Om_nat _ _ j, (Om_lt_Om.2 (natCast_lt_omega0 j)).trans_le hKB.ge⟩
    · rw [hB, rxL_Om hj, hκ, hB2]
  by_cases hW : y = Om ω
  · subst hW
    obtain ⟨hD, hB⟩ := Wr.wrB_OmW (S := S) (n := n)
    have hωN : RxN S (rxW Z' At') ω := by
      have := RxN.phi (RxN.zero (S := S) (T := rxW Z' At')) (RxN.succ (RxN.zero (S := S) (T := rxW Z' At')))
      rwa [veblen_zero_apply, zero_add, opow_one] at this
    refine ⟨hD, by rw [kzL_OmW]; exact hD, ?_, ?_, fun _ _ => by rw [hB]; exact gg_SC_eps (SC_Om omega0_ne_zero)⟩
    · rw [hB]; exact ⟨RxN.om hωN, ConjT.OmW_mem S _ _, hy.2.2⟩
    · rw [hB, kzL_OmW, kzL_OmW, hB]
  have hy1 : Om 1 < y := lt_of_le_of_ne h1 (fun e => hΩ ⟨1, by rw [← e, Nat.cast_one]⟩)
  by_cases hS : SC y
  · have hne : ∀ σ, y ≠ Om σ := fun σ e => by
      rcases kzCard hKB (e ▸ hy.2.2) with ⟨k, rfl⟩ | rfl
      · exact hΩ ⟨k, e⟩
      · exact hW e
    obtain ⟨i, hi, e, heE, hen, rfl, hst⟩ := kzE_atom hKB hT1 hy hS hy1 hne
    obtain ⟨hDe, hDκe, hBeE, hκe, -⟩ := IH e (rxMs_lt_stage (kzE_lt_Lam hKB heE) hst) heE
    have heW : RxEK S (rxW Z At) K e := ⟨heE.1.mono hTW, heE.2⟩
    have hi0 : (i : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    obtain ⟨hDy, hBy, hBen⟩ := Ug.ugB_psiS (n := n) hi0 (vbDnat i) hDe hen
    rw [mwB_nat] at hBy hBen
    have hκy := (kzL_psiE hKB hi heW hen).1
    have hκen := kzL_tr hZ hZ1 hAt hKB hi heW heW hen hen
    have hi1 : (i : Ordinal.{0}) + 1 ≠ 0 := by
      rw [← Nat.cast_succ]; exact_mod_cast (show i + 1 ≠ 0 by omega)
    have hDi1 : MvD S ((i : Ordinal.{0}) + 1) := by rw [← Nat.cast_succ]; exact vbDnat (i + 1)
    obtain ⟨hDκy, hBκy, -⟩ := Ug.ugB_psiS (n := n) hi1 hDi1 hDκe hκen
    have hBi1 : bcB S n ((i : Ordinal.{0}) + 1) = (i : Ordinal.{0}) + 1 := by
      rw [← Nat.cast_succ]; exact mwB_nat n (i + 1)
    rw [hBi1] at hBκy
    refine ⟨hDy, by rw [hκy]; exact hDκy, by rw [hBy]; exact kzE_psi hKB hi hBeE hBen, ?_,
      fun _ _ => by rw [hBy]; exact gg_SC_eps (SC_psi (InR_Om_succ _) _)⟩
    rw [hBy, (kzL_psiE hKB hi hBeE hBen).1, hκe, hκy, hBκy]
  by_cases hε : ω ^ y = y
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hy1 hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hy hv hb
    obtain ⟨hDa, hDκa, hBaE, hκa, -⟩ := IH _ (rxMs_lt_val hha ha) haE
    obtain ⟨hDb, hDκb, hBbE, hκb, -⟩ := IH _ (rxMs_lt_val hhb hb) hbE
    have hab : invVeblen₁ y < veblen (invVeblen₁ y) (invVeblen₂ y) := by rw [hv]; exact ha
    have hbb : invVeblen₂ y < veblen (invVeblen₁ y) (invVeblen₂ y) := by rw [hv]; exact hb
    obtain ⟨hDv, hBv⟩ := mwB_phi (k := n) hDa hDb hab hbb
    rw [hv] at hDv hBv
    have hκy := kzL_veb (Z := Z) (At := At) hyW hy1 hε hS
    have hκa_lt := kzL_mono hZ hZ1 hAt hKB ⟨haE.1.mono hTW, haE.2⟩ hyW ha
    have hκb_lt := kzL_mono hZ hZ1 hAt hKB ⟨hbE.1.mono hTW, hbE.2⟩ hyW hb
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
    have hBE : RxEK S (rxW Z' At') K (bcB S n y) := by
      rw [hBv]
      exact ⟨RxN.phi hBaE.1 hBbE.1, CSet.phi_mem hBaE.2.1 hBbE.2.1, hKB.sc.2 _ hBaE.2.2 _ hBbE.2.2⟩
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
    rw [kzL_veb (Z := Z') (At := At') hBE hBy1 hBε hBS, hpair.1, hpair.2, hκa, hκb, hκy, hBκv]
  -- the Cantor normal form
  obtain ⟨m, hm1, hdm, hκy, hlE, hrE, -, hrlt, hopy, hℓ1, hor, hlh, hrh, -⟩ := kzLDecK hZ hZ1 hAt hKB hyW h1
  have hly : log ω y < y := hor.resolve_left hε
  have hlT : RxEK S T K (log ω y) := (kzE_log hy).1
  have hrT : RxEK S T K (y % ω ^ log ω y) := (kzE_rem hy).1
  have hlh' := (kzE_log hy).2
  have hrh' := (kzE_rem hy).2
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
  obtain ⟨hBE, hκ'B⟩ := kzKg_cnf hZ' hZ1' hAt' hKB m hm1 hBlE hBrE hBl1 hBrlt
  have hlW : RxEK S (rxW Z At) K (log ω y) := ⟨hlT.1.mono hTW, hlT.2⟩
  have hBo' : MvD S (ω ^ rxL S Z At (rxW Z At) (log ω y)) ∧
      bcB S n (ω ^ rxL S Z At (rxW Z At) (log ω y)) = ω ^ bcB S n (rxL S Z At (rxW Z At) (log ω y)) := by
    by_cases he : ω ^ rxL S Z At (rxW Z At) (log ω y) = rxL S Z At (rxW Z At) (log ω y)
    · have hlε : ω ^ log ω y = log ω y := kzKg_eps hZ hZ1 hAt hKB hlW hℓ1 he
      have hBlε := hεl hℓ1 hlε
      have hκBε := kzL_eps hZ' hZ1' hAt' hKB hBlE hBl1 hBlε
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
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx') {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hl' hX' hKB

/-- **THE MOVE OF `T_K`**: `T_{K,λ'}(B_n x) = B_n(T_{K,λ} x)` for `x ∈ D_K` whose image is a member over `T`. -/
theorem vbTK_move {T : Ordinal.{0}} (hT : SC T) (hTW : T ≤ vbW S l)
    (hleaf : ∀ g, g < T → MvD S g ∧ MvD S (ruInv (upsilon l) (ldAtR S l) g) ∧ bcB S n g < vbW S l' ∧
      ruInv (upsilon l') (ldAtR S l') (bcB S n g) = bcB S n (ruInv (upsilon l) (ldAtR S l) g))
    {x : Ordinal.{0}} (hx : VbDK S l K x) (hxT : RxEK S T K (vbTK S l K x)) :
    MvD S x ∧ MvD S (vbTK S l K x) ∧ RxEK S (vbW S l') K (bcB S n (vbTK S l K x)) ∧
      vbK S l' (bcB S n (vbTK S l K x)) = bcB S n x ∧
      vbTK S l' K (bcB S n x) = bcB S n (vbTK S l K x) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  obtain ⟨-, hK⟩ := vbTK_eq hl hX hKB hx
  obtain ⟨hD, hDκ, hBE, hmove, -⟩ := kzK_move (Z := upsilon l) (At := ldAtR S l) (Z' := upsilon l')
    (At' := ldAtR S l') hZ hZ1 (ldAt_GxAt _ _) hZ' hZ1' (ldAt_GxAt _ _) hKB hT hTW hleaf _ hxT
  have hK' : rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (vbTK S l K x) = x := hK
  rw [hK'] at hDκ hmove
  refine ⟨hDκ, hD, hBE, hmove, ?_⟩
  have h := vbTK_K hl' hX' hKB hBE
  rwa [show vbK S l' (bcB S n (vbTK S l K x)) = bcB S n x from hmove] at h

end Rst

/-- **A member of `Cl(B, Z)` is normal over `Z`** when `ψ₁(B) < Z ≤ Ω₁`. -/
theorem kzN_cl {Z B : Ordinal.{0}} (hZ1 : Z ≤ Om 1) (hZ : S.psi B (Om 1) < Z) {y : Ordinal.{0}}
    (hy : y ∈ S.CSet B Z) : RxN S Z y := by
  induction hy with
  | small h => exact RxN.small h
  | zero => exact RxN.zero
  | inacc n => exact RxN.inacc n
  | inaccW => exact RxN.inaccW
  | add _ _ ihx ihy => exact RxN.add ihx ihy
  | phi _ _ ihx ihy => exact RxN.phi ihx ihy
  | om _ ih => exact RxN.om ih
  | @coll π e hπ hπC heC ihπ ihe =>
    show RxN S Z (S.psi e.1 π)
    by_cases h1 : π = Om 1
    · subst h1
      exact RxN.small (lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one e.2.le).1 hZ)
    · exact rxN_psi hZ1 e.1 ihe π hπ h1 ihπ

section RstA

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hKB hA hρ

/-- **`T_K x` is a member over `Θ(ψ₂ a)`** for every `x ∈ D_K ∩ Cl(a, ψ₂ a)`, `a ≤ A`. -/
theorem kzTE {a : Ordinal.{0}} (haA : a ≤ A) : ∀ x, VbDK S l K x → x ∈ S.CSet a (S.psi a (Om (1 + 1))) →
    RxEK S (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) K (vbTK S l K x) := by
  intro x hx hxC
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set Z := gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) with hZdef
  have hZ1 : Z ≤ Om 1 :=
    (gxTh_mono (psi_lt hκ2 a).le).trans (vbZ2_le hl hX)
  have hZ0 : S.psi (A + 1) (Om 1) ≤ Z := by
    rw [← ldBlk_zero hA hρ]; exact gxTh_mono (psi_mono hκ2 zero_le).1
  have hAZ : S.psi A (Om 1) < Z :=
    (psi_lt_psi_of_mem hκ1 (lt_add_one A) ((psi_mono hκ1 le_self_add).2 hA)).trans_le hZ0
  have hmem : vbTK S l K x ∈ S.CSet A Z := by
    refine kzT_cl hl hX hKB (psi_lt hκ2 a).le
      (fun e he hea => (vbTK_le_self hl hX hKB he).trans_lt (hea.trans_le haA))
      (fun c hc hc2 hcC => ?_) x hx hxC
    rw [vbTK_code hl hX hKB hc2 hc.1]
    exact CSet.of_lt (gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2))
  exact ⟨kzN_cl hZ1 hAZ hmem, (vbTK_mem hl hX hKB hx).1, (vbTK_mem hl hX hKB hx).2⟩

end RstA

section MoveA

variable {n : ℕ} {l l' ηx ηx' A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Pv S ηx') {K : Ordinal.{0}} (hKB : KzB S K)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hl' hX' hKB hA hρ

/-- **The leaf hypothesis of `Kz.vbTK_move` below `Θ(ψ₂ a)`** from the moves of the codes below `ψ₂ a`
(`Xq.xqLeaf` with the bound `B_n x < P′`). -/
theorem kzLeaf {a : Ordinal.{0}}
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ g, g < gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) →
      MvD S g ∧ MvD S (Ru.ruInv (upsilon l) (ldAtR S l) g) ∧ Bc.bcB S n g < vbW S l' ∧
      Ru.ruInv (upsilon l') (ldAtR S l') (Bc.bcB S n g) = Bc.bcB S n (Ru.ruInv (upsilon l) (ldAtR S l) g) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  refine vbLeaf_of_codes hl hX hl' hX' hTW fun c hc hc2 hcT => ?_
  have hcs : c < S.psi a (Om (1 + 1)) := by
    by_contra h
    exact absurd hcT (not_lt.2 (gxTh_mono (not_lt.1 h)))
  obtain ⟨hD, hc', hB, hΘ, hmv⟩ := IH c hc hcs
  exact ⟨hD, mvD_of_lt (hΘ.trans (Bc.bcC_lt S (n + 1))), hc', hB.trans (psi_lt hκ2 _), hmv⟩

/-- **THE MOVE OF `T_K`** at a wall atom `ψ₂ a`, `a ≤ A`: under the moves of the codes below `ψ₂ a`,
`T_{K,λ'}(B_n x) = B_n(T_{K,λ} x)` for every `x ∈ D_K ∩ Cl(a, ψ₂ a)`. -/
theorem kzTMove {a : Ordinal.{0}} (haA : a ≤ A)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbDK S l K x → x ∈ S.CSet a (S.psi a (Om (1 + 1))) →
      MvD S x ∧ MvD S (vbTK S l K x) ∧ RxEK S (vbW S l') K (Bc.bcB S n (vbTK S l K x)) ∧
        vbK S l' (Bc.bcB S n (vbTK S l K x)) = Bc.bcB S n x ∧
        vbTK S l' K (Bc.bcB S n x) = Bc.bcB S n (vbTK S l K x) := by
  intro x hx hxC
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := Le.leRho hl hX
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 a) (hρ1.trans (psiS_bounds (S := S) a 1).1)
  exact vbTK_move (n := n) hl hX hl' hX' hKB hSC hTW
    (kzLeaf hl hX hl' hX' hKB hA hρ IH) hx (kzTE hl hX hKB hA hρ haA x hx hxC)

end MoveA

end Googology.Trans.PoR.InaccPsi.R2.Kz
