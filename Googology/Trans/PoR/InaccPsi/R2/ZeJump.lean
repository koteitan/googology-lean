import Googology.Trans.PoR.InaccPsi.R2.ZeName
import Googology.Trans.PoR.InaccPsi.R2.YzJump

/-!
# No jump of `B_n` at a range restart: `Xw.XwJumpNoRng` from CapV in `(L(ω), L(ω+1))`

Notation as in `R2.YkJump`, `R2.YzJump`: an instance `(n, R, R', s)` of `Xw.XwJumpNoRng` (chain points of
`(R, R')` cofinal below `s`, `lh(s) = R`, `B_n` jumps at `s`, `s` a range restart), `s* = sup_{q<s} B_n q = ρ_κ` its
gap bottom (`Yk.ykGapBot`: `κ` a range restart, `r(κ) = R'`, `B_n q < ρ_κ` for `q < s`).

* `zeJump_false` (**no instance exists, given CapV in `(L(ω), L(ω+1))`**): by the cap window `Ze.zeCap_win` at
  `κ` there is `x < ρ_κ` with `cap(μ) ≤ ρ_κ` for every restart `ρ_μ ∈ (x, ρ_κ)`; the chain images
  `B_n y = ρ_{μ'}` are cofinal below `ρ_κ`, they are range restarts above `L(ω)` with `r(μ') = R'`; take one above
  `x`: CapV gives `R' = r(μ') < cap(μ') ≤ ρ_κ < r(κ) = R'`.  Both code cases at once (short and long gap bottoms).
* `zeJumpShortU` (**`Yz.YzJumpShort S`, UNCONDITIONAL**: `zeJump_short_false`, near `ρ_κ` the chain images have
  codes `< θ·ω` by `Ze.zeCode_win`, so `r(μ') < υ_{μ'+ω+2} < ρ_κ < r(κ)`);
* `zeJumpNoRng` (**`Xw.XwJumpNoRng S`** from the frontier hypothesis `hVt` of the road), `zeJumpShort`,
  `zeJumpLong` (`Yz.YzJumpShort S`, `Yz.YzJumpLong S`), `zeEQJump` (**`Xr.XrJump S`**, with
  `Ye.yeJumpOff`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The chain images near the gap bottom**: at an instance, `s* = ρ_κ` (`κ` a range restart, `r(κ) = R'`) and
for every `x < ρ_κ` there is a chain image `ρ_{μ'} = B_n y ∈ (x, ρ_κ)`, `μ'` a range restart above `L(ω)` with
`r(μ') = R'`. -/
theorem zeJump_img (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) :
    ∃ κ, CdRange S κ ∧ sSup (Bc.bcB S n '' Iio s) = upsilon κ ∧ cdR S κ = R' ∧
      ∀ x < upsilon κ, ∃ μ', CdRange S μ' ∧ x < upsilon μ' ∧
        upsilon μ' < upsilon κ ∧ Nc.ncL S ω < upsilon μ' ∧ cdR S μ' = R' := by
  obtain ⟨κ, hκ, he, hRκ, -, -, hlt, -⟩ := Yk.ykGapBot hν hU hL hRc h1s hcof hsR hjump
  refine ⟨κ, hκ, he, hRκ, fun x hxκ => ?_⟩
  have hsRle : s ≤ R := hsR.2 s (le1_refl s)
  have hsc : s < Bc.bcC S (n + 1) := hsRle.trans_lt hRc
  have hBlt : ∀ {a b : Ordinal.{0}}, a < Bc.bcC S (n + 1) → b < Bc.bcC S (n + 1) → a < b →
      Bc.bcB S n a < Bc.bcB S n b := fun ha hb hab =>
    (Bc.bcB_lt_iff (ha.trans (Bc.bcC_lt S (n + 1))) (hb.trans (Bc.bcC_lt S (n + 1)))).2 hab
  have hbdd : BddAbove (Bc.bcB S n '' Iio s) := ⟨Bc.bcB S n s, by
    rintro _ ⟨q, hq, rfl⟩; exact (hBlt ((show q < s from hq).trans hsc) hsc hq).le⟩
  have hTne : (Bc.bcB S n '' Iio s).Nonempty := ⟨_, Bc.bcC S n, h1s, rfl⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, hxq⟩ := (lt_csSup_iff hbdd hTne).1 (he ▸ hxκ)
  obtain ⟨y, hqy, hys, μ, μ', hμ, h1, rfl, -, hμ', hB, hR'⟩ := hcof q hq
  have hyc : upsilon μ < Bc.bcC S (n + 1) := hys.trans hsc
  have hμR : CdRange S μ' := Xn.xnRange_img hμ h1 hyc hμ' hB
  have hxμ : x < upsilon μ' := hB ▸ hxq.trans (hBlt ((show q < s from hq).trans hsc) hyc hqy)
  have hμκ : upsilon μ' < upsilon κ := hB ▸ hlt _ hys
  have hLμ : Nc.ncL S ω < upsilon μ' := by
    have hB0 : Bc.bcB S n (Bc.bcC S n) = Nc.ncL S ω := by
      rw [show Bc.bcC S n = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) from rfl, Bc.bcB_base]
    rw [← hB, ← hB0]
    exact hBlt (h1.trans hyc) hyc h1
  exact ⟨μ', hμR, hxμ, hμκ, hLμ, hR'⟩

/-- **No jump instance at a range restart**, given CapV at the range restarts of `(L(ω), L(ω+1))`. -/
theorem zeJump_false (hV : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q) : False := by
  obtain ⟨κ, hκ, -, hRκ, himg⟩ := zeJump_img hν hU hL hRc h1s hcof hsR hjump
  obtain ⟨x, hxκ, hwin⟩ := zeCap_win hκ.1 hκ.2.2.1
  obtain ⟨μ', hμR, hxμ, hμκ, hLμ, hR'⟩ := himg x hxκ
  have hcap := zeReach_lt_cap (hV μ' hμR hLμ) (hwin μ' hμR.1 hxμ hμκ)
  rw [hR', ← hRκ] at hcap
  exact absurd (hcap.trans (cdRho_lt_R S κ)) (lt_irrefl _)

/-- **No jump instance with a short-code gap bottom** (no CapV needed): near `ρ_κ` the chain images have codes
`< θ·ω` (`Ze.zeCode_win`), so `r(μ') < υ_{μ'+ω+2} < ρ_κ < r(κ)` (`Yz.yzR_lowCode`), against `r(μ') = R' = r(κ)`. -/
theorem zeJump_short_false (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) {n : ℕ}
    {R R' s κ : Ordinal.{0}} (hRc : R < Bc.bcC S (n + 1)) (h1s : Bc.bcC S n < s)
    (hcof : ∀ x < s, ∃ y, x < y ∧ y < s ∧ Xr.XrPt S n R R' y) (hsR : IsReach R2C s R)
    (hjump : ∃ Q < Bc.bcB S n s, ∀ q < s, Bc.bcB S n q ≤ Q)
    (he : sSup (Bc.bcB S n '' Iio s) = upsilon κ) (hm : cdCode S κ ≤ ConjT.th S * ω) : False := by
  obtain ⟨κ₀, hκ, he₀, hRκ, himg⟩ := zeJump_img hν hU hL hRc h1s hcof hsR hjump
  have hk0 : κ₀ = κ := Tp.tpUps_inj (he₀.symm.trans he)
  subst hk0
  obtain ⟨x, hxκ, hwin⟩ := zeCode_win hκ.1 hκ.2.2.1 hm
  obtain ⟨μ', hμR, hxμ, hμκ, -, hR'⟩ := himg x hxκ
  have hcode := hwin μ' hμR.1 hxμ hμκ
  have hlt := Yz.yz_ri_add_lt hμR.1 hκ.1 (Tp.tpUps_lt_iff.1 hμκ)
  have hup : upsilon (μ' + (ω + 2)) < upsilon κ₀ := upsilon_normal.strictMono hlt
  have hC : upsilon (μ' + ω + 1) < nuC := by
    have h1 : μ' + ω + 1 < μ' + (ω + 2) := by
      rw [add_assoc]; exact (add_lt_add_iff_left μ').2 ((add_lt_add_iff_left ω).2 one_lt_two)
    exact ((upsilon_normal.strictMono h1).trans hup).trans (hκ.2.2.1.trans_le hν)
  have hr := Yz.yzR_lowCode hμR.1 hμR.2.2.1 hC hcode.le
  rw [hR', ← hRκ] at hr
  exact absurd ((hr.trans hup).trans (cdRho_lt_R S κ₀)) (lt_irrefl _)

/-- **`Xw.XwJumpNoRng S`** from the frontier hypothesis `hVt` of the road. -/
theorem zeJumpNoRng
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l) :
    Xw.XwJumpNoRng S :=
  fun _ _ _ _ hν hU hL _ _ _ hRc _ h1s hcof _ hsR hjump _ =>
    zeJump_false (zeCapHigh hVt) hν hU hL hRc h1s hcof hsR hjump

/-- **`Yz.YzJumpShort S` (UNCONDITIONAL)**: no jump instance has a short-code gap bottom. -/
theorem zeJumpShortU : Yz.YzJumpShort S :=
  fun _ _ _ _ _ hν hU hL _ _ _ hRc _ h1s hcof _ hsR hjump _ _ he hm =>
    zeJump_short_false hν hU hL hRc h1s hcof hsR hjump he hm

/-- **`Yz.YzJumpShort S`** (short-code gap bottoms) from `hVt`. -/
theorem zeJumpShort
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l) :
    Yz.YzJumpShort S :=
  (Yz.yzJumpNoRng_iff.1 (zeJumpNoRng hVt)).1

/-- **`Yz.YzJumpLong S`** (long-code gap bottoms) from `hVt`. -/
theorem zeJumpLong
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l) :
    Yz.YzJumpLong S :=
  (Yz.yzJumpNoRng_iff.1 (zeJumpNoRng hVt)).2

/-- **`Xr.XrJump S`** (the jumps of `B_n` never break EQ) from `hVt` (with `Ye.yeJumpOff`). -/
theorem zeEQJump
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l) :
    Xr.XrJump S :=
  Xw.xwJump_of Ye.yeJumpOff (zeJumpNoRng hVt)

end Googology.Trans.PoR.InaccPsi.R2.Ze
