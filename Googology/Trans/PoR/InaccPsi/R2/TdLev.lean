import Googology.Trans.PoR.InaccPsi.R2.TdRoad

/-!
# Code levels: the tools for nodes `φ(c, Ω₂ + Y)` whose level `c` is a code moved by `Θ` and `B_n`

`φ = veblen`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, codes = `Le.LeCl κ Q` (`κ`, `Q` strongly critical), `H_λ = cdHull S λ`,
`Θ = gxTh ρ_λ (ldAtR λ)` (the order type of the codes; `Θ x = x` below `ρ_λ`).

* `tdCl_lt` (**a code below its generator `κ` is below its bound `Q`**), `tdCl_lev` (**THE LEVEL OF A CODE IS A
  CODE**: `φ(a, y)` a code with `y < φ(a, y)` gives `a` a code), `tdCl_lev_lt` (so `a < Q` when `a < κ`);
* `tdCl_levDec` (**THE FINE CLOSURE LAW IN THE LEVEL ARGUMENT**: at a limit level `c`, a code `w < φ(c, z+1)` is
  below `φ(c', φ(c, z) + 1)` for a code `c' < c`), `tdHull_levDec` (the same for the members of a closure: the
  members `φ(c', ·)` indexed by the hull elements `c' < c` are cofinal **among the hull elements**);
* `tdShp_vebG` (**THE LIFT THROUGH `φ(a, ·)` WITH A MOVING LEVEL**: value level `a`, image level `â`, each with its
  own data above the bottoms; `Td.tdShp_veb` is the case `a = â < K`), `tdShp_vebC` (**at a code level
  `1 ≤ a < bot` of `λ`, image level `Θ a`: all the data hold**);
* `tdNode_nfW` (**every `W`-fixed point `1 ≤ E < φ(Ω₂, 1)` is a node `φ(a, y)` with a level `a < Ω₂`**,
  `Ω₂ < y < E`), `tdNode_lev` (the level of a node in `H_λ` is in `H_λ`; of a code, a code below `Q`);
* `tdIL`, `tdThL` (**the image with the levels read by `Θ`**: `φ(a, Ω₂ + Y) ↦ φ(Θ a, Ω₁ + Ŷ)`), `tdIL_eq`,
  `tdThL_eq` (**it is `Ta.taTh` below `φ(K, Ω₂ + 1)`**), `tdThL_node` (the φ law with the level read),
  `tdThL_lev` (`Θ a = a` for `a < ρ_λ`, so the levels below `ρ_λ` are kept), `tdThL_veb`;
* `tdB_nodeL` (**THE MOVE OF A NODE WITH A CODE LEVEL**: `B_n φ(a, Ω₂ + z) = φ(B_n a, Ω₂ + B_n z)` and
  `Θ̂'_L(B_n E) = B_n(Θ̂_L E)` from the moves of `a` and `z`).

No new axiom.  New definitions: `tdIL`, `tdThL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-! ## Codes below the generator and the level of a code -/

section Code

variable {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ)

include hQ in
/-- **A code below its generator `κ` is below its bound `Q`.** -/
theorem tdCl_lt : ∀ x, LeCl κ Q x → x < κ → x < Q := by
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h
    exact hQ.isPrincipal (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
  | @phi p q _ _ ihp ihq =>
    intro h
    exact hQ.2 p (ihp ((left_le_veblen p q).trans_lt h)) q (ihq ((right_le_veblen p q).trans_lt h))

include hκ in
/-- **THE LEVEL OF A CODE IS A CODE**: `φ(a, y)` a code with `y < φ(a, y)` gives `a` a code. -/
theorem tdCl_lev : ∀ w, LeCl κ Q w → ∀ a y, w = veblen a y → y < w → LeCl κ Q a := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he _
    exact LeCl.small ((left_le_veblen a y).trans_lt (he ▸ hwQ))
  | om =>
    intro a y he hy
    rcases lt_or_ge a κ with haκ | hκa
    · have hy' : y < κ := hy
      have : veblen a y < κ := hκ.2 a haκ y hy'
      rw [← he] at this; exact absurd this (lt_irrefl _)
    · have : a ≤ κ := by rw [he]; exact left_le_veblen a y
      rw [le_antisymm this hκa]; exact LeCl.om
  | @add x z _ _ ihx ihz =>
    intro a y he hy
    by_cases hz : z = x + z
    · exact ihz a y (hz.trans he) (hz ▸ hy)
    · by_cases hx : x = x + z
      · exact ihx a y (hx.trans he) (hx ▸ hy)
      · have hzl : z < x + z := lt_of_le_of_ne le_add_self hz
        have hxl : x < x + z := lt_of_le_of_ne le_self_add hx
        rw [he] at hzl hxl
        have := Ph.ph_veblen_prin a y hxl hzl
        rw [← he] at this; exact absurd this (lt_irrefl _)
  | @phi p q hp _ _ ihq =>
    intro a y he hy
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hfix : veblen p (veblen a y) = veblen a y := veblen_veblen_of_lt hpa y
      have hq : q = veblen a y := by
        have h2 : veblen p q = veblen p (veblen a y) := by rw [hfix]; exact he
        exact veblen_injective p h2
      exact ihq a y hq (by rw [hq]; rw [← he]; exact hy)
    · exact hp
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      rw [he] at hfix
      have hyy : veblen a y = y := veblen_injective a hfix
      rw [he, hyy] at hy; exact absurd hy (lt_irrefl _)

include hQ hκ in
/-- The level `a < κ` of a code `φ(a, y)` (`y < φ(a, y)`) is below the bound `Q`. -/
theorem tdCl_lev_lt {a y : Ordinal.{0}} (h : LeCl κ Q (veblen a y)) (hy : y < veblen a y) (haκ : a < κ) : a < Q :=
  tdCl_lt hQ a (tdCl_lev hκ _ h a y rfl hy) haκ

include hQ hκ in
/-- **THE FINE CLOSURE LAW IN THE LEVEL ARGUMENT**: at a limit level `c`, a code `w < φ(c, z+1)` is below
`φ(c', φ(c, z) + 1)` for a code `c' < c`. -/
theorem tdCl_levDec {c z : Ordinal.{0}} (hc : IsSuccLimit c) :
    ∀ w, LeCl κ Q w → w < veblen c (z + 1) → ∃ c', LeCl κ Q c' ∧ c' < c ∧ w < veblen c' (veblen c z + 1) := by
  have hc0 : 0 < c := hc.bot_lt
  have triv : ∀ w, w ≤ veblen c z → ∃ c', LeCl κ Q c' ∧ c' < c ∧ w < veblen c' (veblen c z + 1) := by
    intro w hw
    refine ⟨0, LeCl.zero hQ.1, hc0, ?_⟩
    exact hw.trans_lt ((lt_add_one _).trans_le (right_le_veblen 0 _))
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    rcases le_or_gt w (veblen c z) with h | h
    · exact triv w h
    · obtain ⟨a', ha', hwa⟩ := taVeb_lim_cof hc hlt
      have hcQ : c < Q := ((left_le_veblen c z).trans_lt h).trans hwQ
      exact ⟨a', LeCl.small (ha'.trans hcQ), ha', hwa⟩
  | om =>
    intro hlt
    refine triv κ ?_
    rcases lt_or_ge c κ with hcκ | hκc
    · have hfix : veblen c κ = κ := hκ.veblen_right hcκ
      by_contra hcon
      push Not at hcon
      have hzκ : z < κ := by
        by_contra h'
        push Not at h'
        have := (veblen_le_veblen_iff_right (o := c)).2 h'
        rw [hfix] at this; exact absurd hcon (not_lt.2 this)
      have : veblen c (z + 1) ≤ veblen c κ :=
        (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hzκ)
      rw [hfix] at this; exact absurd hlt (not_lt.2 this)
    · exact hκc.trans (left_le_veblen c z)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · refine ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · refine ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmcl : LeCl κ Q m := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, LeCl.add hmcl (LeCl.small (gg_one_lt_of_SC hQ)), hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) (veblen c z + 1) :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) (veblen c z + 1)) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) (veblen c z + 1) := veblen_veblen_of_lt hpm _
    · refine triv _ ((veblen_le_veblen_iff_right).2 ?_)
      exact Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
    · refine triv _ ?_
      have hfix : veblen c (veblen p q) = veblen p q := veblen_veblen_of_lt hpc q
      rw [← hfix] at hlt
      have h1 := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
      exact h1.trans (right_le_veblen c z)

end Code

/-- **The fine level decomposition for the members of a closure**: at a limit level `c`, a member `x < φ(c, z+1)`
is below `φ(c', φ(c, z) + 1)` for a member `c' < c`. -/
theorem tdHull_levDec {A B c z : Ordinal.{0}} (hc : IsSuccLimit c) :
    ∀ x, x ∈ S.CSet A B → x < veblen c (z + 1) →
      ∃ c' ∈ S.CSet A B, c' < c ∧ x < veblen c' (veblen c z + 1) := by
  have hc0 : 0 < c := hc.bot_lt
  have triv : ∀ x, x ≤ veblen c z → ∃ c' ∈ S.CSet A B, c' < c ∧ x < veblen c' (veblen c z + 1) := by
    intro x hx
    refine ⟨0, CSet.zero_mem _ _, hc0, ?_⟩
    exact hx.trans_lt ((lt_add_one _).trans_le (right_le_veblen 0 _))
  have hSC : ∀ w, SC w → w < veblen c (z + 1) → w ≤ veblen c z := by
    intro w hw hlt
    rcases lt_or_ge c w with hcw | hwc
    · have hfix : veblen c w = w := hw.veblen_right hcw
      have h1 : w < z + 1 := by
        have h2 := hlt; rw [← hfix] at h2; exact (veblen_lt_veblen_iff_right).1 h2
      exact (Order.lt_add_one_iff.1 h1).trans (right_le_veblen c z)
    · exact hwc.trans (left_le_veblen c z)
  intro x hx
  induction hx with
  | @small x hxB =>
    intro hlt
    rcases le_or_gt x (veblen c z) with h | h
    · exact triv x h
    · obtain ⟨a', ha', hxa⟩ := taVeb_lim_cof hc hlt
      have hcB : c < B := ((left_le_veblen c z).trans_lt h).trans hxB
      exact ⟨a', CSet.of_lt (ha'.trans hcB), ha', hxa⟩
  | zero => intro _; exact triv 0 zero_le
  | inacc n => intro hlt; exact triv _ (hSC _ (SC_I n) hlt)
  | inaccW => intro hlt; exact triv _ (hSC _ SC_Iw hlt)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · exact ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · exact ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmm : m ∈ S.CSet A B := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, CSet.succ_mem hmm, hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) (veblen c z + 1) :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) (veblen c z + 1)) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) (veblen c z + 1) := veblen_veblen_of_lt hpm _
    · refine triv _ ((veblen_le_veblen_iff_right).2 ?_)
      exact Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
    · refine triv _ ?_
      have hfix : veblen c (veblen p q) = veblen p q := veblen_veblen_of_lt hpc q
      rw [← hfix] at hlt
      have h1 := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 hlt)
      exact h1.trans (right_le_veblen c z)
  | @om x hx _ =>
    intro hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · exact triv _ (by rw [Om_zero]; exact zero_le)
    · exact triv _ (hSC _ (SC_Om hx0) hlt)
  | @coll π e hπ _ _ _ _ =>
    intro hlt
    exact triv _ (hSC _ (SC_psi hπ e.1) hlt)

/-! ## The lift through `φ(a, ·)` with a moving level -/

section Lift

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs bot both : Ordinal.{0}}

include hl hX

/-- **THE LIFT THROUGH `φ(a, ·)` WITH A MOVING LEVEL**: `ζ ↦ φ(a, g ζ)` with the image `v ↦ φ(â, ĝ v)`, for a
value level `a < Ω₂` in `H_λ` with its data above `bot` and an image level `â < Ω₁` with its data above `b̂ot`. -/
theorem tdShp_vebG {a ah : Ordinal.{0}} (h : TaShp S l g gh gs ghs bot both)
    (ha0 : a ≠ 0) (haW : a < Om (1 + 1)) (haH : a ∈ cdHull S l) (hamem : ∀ c, bot ≤ c → a ∈ S.CSet 0 c)
    (hacl : ∀ Q, SC Q → bot ≤ Q → LeCl (Om (1 + 1)) Q a)
    (hah0 : ah ≠ 0) (hahO : ah < Om 1) (hahmem : ∀ c, both ≤ c → ah ∈ S.CSet 0 c)
    (hahcl : ∀ Q, SC Q → both ≤ Q → LeCl (Om 1) Q ah)
    (hgs : Om (1 + 1) < gs) (hghs : Om 1 < ghs) :
    TaShp S l (fun z => veblen a (g z)) (fun v => veblen ah (gh v)) (veblen a gs) (veblen ah ghs) bot both := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hWs : Om (1 + 1) * veblen a gs = veblen a gs :=
    Ta.taK_mul_veb ldOm2_SC ha0 (hgs.trans_le (right_le_veblen a gs))
  have hOs : Om 1 * veblen ah ghs = veblen ah ghs :=
    Ta.taK_mul_veb Ph.ph_SC_Om1 hah0 (hghs.trans_le (right_le_veblen ah ghs))
  have hfine : ∀ Q, SC Q → bot ≤ Q → TaFine (fun z => veblen a (g z)) (veblen a gs) Q := by
    intro Q hQ hQb y hy hlt
    obtain ⟨u, hu, hugs, hyu⟩ := taCl_dec hQ ldOm2_SC haW h.lim y hy hlt
    obtain ⟨ζ, hζ, huζ⟩ := h.fine Q hQ hQb u hu hugs
    exact ⟨ζ, hζ, hyu.trans ((veblen_lt_veblen_iff_right).2 huζ)⟩
  have hfineh : ∀ Q, SC Q → both ≤ Q → TaFineH (fun v => veblen ah (gh v)) (veblen ah ghs) Q := by
    intro Q hQ hQb y hy hlt
    obtain ⟨u, hu, hugs, hyu⟩ := taCl_dec hQ Ph.ph_SC_Om1 hahO h.limh y hy hlt
    obtain ⟨v, hv, huv⟩ := h.fineh Q hQ hQb u hu hugs
    exact ⟨v, hv, hyu.trans ((veblen_lt_veblen_iff_right).2 huv)⟩
  refine ⟨⟨fun x y hxy => (veblen_lt_veblen_iff_right).2 (h.shp.st hxy),
    fun ζ hζ => (veblen_lt_veblen_iff_right).2 (h.shp.lt ζ hζ),
    fun v hv => (veblen_lt_veblen_iff_right).2 (h.shp.lth v hv),
    h.shp.inf.trans (right_le_veblen a gs), h.shp.infh.trans (right_le_veblen ah ghs),
    fun ζ hζ hζW => CSet.phi_mem haH (h.shp.hull ζ hζ hζW),
    CSet.phi_mem haH h.shp.hullS,
    fun x c hx hc => CSet.phi_mem (hamem c hc) (h.shp.mem x c hx hc),
    fun v c hv hc => CSet.phi_mem (hahmem c hc) (h.shp.memh v c hv hc),
    fun Q hQ hQb w hw hlt => ?_, fun Q hQ hQb w hw hlt => ?_, fun c hc hcs => ?_,
    fun Q hQ hQb ζ hζ => LeCl.phi (hacl Q hQ hQb) (h.shp.clm Q hQ hQb ζ hζ),
    fun Q hQ hQb v hv => LeCl.phi (hahcl Q hQ hQb) (h.shp.clmh Q hQ hQb v hv),
    fun x y hxy => (veblen_lt_veblen_iff_right).2 (h.shp.sth hxy), fun v hv u hu => ?_,
    fun c hc => CSet.phi_mem (hamem c hc) (h.shp.memS c hc),
    fun c hc => CSet.phi_mem (hahmem c hc) (h.shp.memhS c hc),
    fun Q hQ hQb => LeCl.phi (hacl Q hQ hQb) (h.shp.clS Q hQ hQb),
    fun Q hQ hQb => LeCl.phi (hahcl Q hQ hQb) (h.shp.clhS Q hQ hQb)⟩,
    taVeb_lim ha0, taVeb_lim hah0, hfine, hfineh⟩
  · rw [hWs] at hlt
    obtain ⟨ζ, hζ, hwζ⟩ := hfine Q hQ hQb w hw hlt
    exact ⟨ζ, hζ, hwζ.trans_le (Ordinal.le_mul_right _ ldOm2_SC.1)⟩
  · rw [hOs] at hlt
    obtain ⟨v, hv, hwv⟩ := hfineh Q hQ hQb w hw hlt
    exact ⟨v, hv, hwv.trans_le (Ordinal.le_mul_right _ (Om_pos one_ne_zero))⟩
  · by_cases h0 : veblen a 0 ≤ c
    · obtain ⟨u, hu, h1, h2⟩ := tdHull_idx hc h0
      have hugs : u < gs := (veblen_lt_veblen_iff_right).1 (h1.trans_lt hcs)
      obtain ⟨q, hq, hqW, huq, hqu⟩ := h.shp.idx u hu hugs
      refine ⟨q, hq, hqW, h2.trans_le ((veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt huq)), ?_⟩
      exact fun hq0 => ((veblen_le_veblen_iff_right).2 (hqu hq0)).trans h1
    · push Not at h0
      refine ⟨0, GxCl.zero hρSC.1, ldOm2_SC.1, h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le), ?_⟩
      exact fun h' => absurd rfl h'
  · have hlimv : IsSuccLimit (gh v) := scLim_of_cont h.shp.sth h.shp.cont hv
    obtain ⟨w, hw, huw⟩ := ((isNormal_veblen ah).lt_iff_exists_lt hlimv).1 hu
    obtain ⟨v', hv', hwv'⟩ := h.shp.cont v hv w hw
    exact ⟨v', hv', huw.trans ((veblen_lt_veblen_iff_right).2 hwv')⟩

/-- **THE LIFT THROUGH `φ(a, ·)` AT A CODE LEVEL BELOW THE BOTTOM**: a code `1 ≤ a < Ω₂` of `λ` with `a < bot`
(read `Θ a`, image bottom `Θ bot`) has all the data of `tdShp_vebG`: `ζ ↦ φ(a, g ζ)`, image `v ↦ φ(Θ a, ĝ v)`. -/
theorem tdShp_vebC {a : Ordinal.{0}} (h : TaShp S l g gh gs ghs bot (gxTh (upsilon l) (ldAtR S l) bot))
    (ha1 : 1 ≤ a) (haW : a < Om (1 + 1)) (hac : GxCl (upsilon l) (ldAtR S l) a) (hab : a < bot)
    (hgs : Om (1 + 1) < gs) (hghs : Om 1 < ghs) :
    TaShp S l (fun z => veblen a (g z)) (fun v => veblen (gxTh (upsilon l) (ldAtR S l) a) (gh v))
      (veblen a gs) (veblen (gxTh (upsilon l) (ldAtR S l) a) ghs) bot (gxTh (upsilon l) (ldAtR S l) bot) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hΘa1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) a := hΘ1 ▸ gxTh_mono ha1
  have hΘab : gxTh (upsilon l) (ldAtR S l) a < gxTh (upsilon l) (ldAtR S l) bot := gxTh_lt hac hab
  exact tdShp_vebG hl hX h (zero_lt_one.trans_le ha1).ne' haW ((ldHull_iff hl hX haW).2 hac)
    (fun c hc => CSet.of_lt (hab.trans_le hc)) (fun Q _ hQ => LeCl.small (hab.trans_le hQ))
    (zero_lt_one.trans_le hΘa1).ne' (Sn.snTh_lt_Om1 hl hX haW.le) (fun c hc => CSet.of_lt (hΘab.trans_le hc))
    (fun Q _ hQ => LeCl.small (hΘab.trans_le hQ)) hgs hghs

end Lift

/-! ## The nodes below `φ(Ω₂, 1)` -/

/-- **Every `W`-fixed point `1 ≤ E < φ(Ω₂, 1)` is a node** `φ(inv₁ E, inv₂ E)` with a level `inv₁ E < Ω₂`
and `Ω₂ < inv₂ E < E`. -/
theorem tdNode_nfW {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < veblen (Om (1 + 1)) 1) (hfix : ¬ sgLW E < E) :
    1 ≤ invVeblen₁ E ∧ invVeblen₁ E < Om (1 + 1) ∧ Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E ∧
      veblen (invVeblen₁ E) (invVeblen₂ E) = E := by
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hle : sgLW E ≤ E :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E)
  have heq : sgLW E = E := le_antisymm hle (not_lt.1 hfix)
  have hWE : leWe E ≤ E := by have h0 := sgLW_le (zero_lt_one.trans_le hE1); rwa [heq] at h0
  have h2 : E ≤ Om (1 + 1) * E := Ordinal.le_mul_right E ldOm2_SC.1
  have h3 : Om (1 + 1) * E ≤ leWe E := right_le_opow _ one_lt_omega0
  have hm : Om (1 + 1) * E = E := le_antisymm (h3.trans hWE) h2
  have hfixω : ω ^ E = E := by
    refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
    calc ω ^ E = leWe E := by unfold leWe; rw [hm]
      _ ≤ E := hWE
  have hΩE : Om (1 + 1) < E := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · calc Om (1 + 1) = Om (1 + 1) * 1 := (mul_one _).symm
        _ ≤ Om (1 + 1) * E := mul_le_mul_right hE1 _
        _ = E := hm
    · have : Om (1 + 1) * 1 < Om (1 + 1) * Om (1 + 1) := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hW1
      rw [mul_one, e] at this
      rw [e] at hm
      rw [hm] at this
      exact lt_irrefl _ this
  have hval : veblen (invVeblen₁ E) (invVeblen₂ E) = E := by rw [veblen_invVeblen₁_invVeblen₂, hfixω]
  have hlt2 : invVeblen₂ E < E := by have := invVeblen₂_lt E; rwa [hfixω] at this
  have h1a : 1 ≤ invVeblen₁ E := by
    refine mem_range_veblen_iff_le_invVeblen₁.1 ?_
    rw [hfixω]
    refine (mem_range_veblen one_ne_zero).2 fun b hb => ?_
    rw [Order.lt_one_iff] at hb; subst hb; rw [veblen_zero_apply]; exact hfixω
  have hg : invVeblen₁ E < Om (1 + 1) := by
    by_contra hc
    push Not at hc
    have hr : ω ^ E ∈ range (veblen (Om (1 + 1))) := mem_range_veblen_iff_le_invVeblen₁.2 hc
    rw [hfixω] at hr
    obtain ⟨z, hz⟩ := hr
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [ldOm2_SC.veblen_zero] at hz
      rw [hz] at hΩE; exact lt_irrefl _ hΩE
    have : veblen (Om (1 + 1)) 1 ≤ E := by
      rw [← hz]; exact (veblen_le_veblen_iff_right).2 (Order.one_le_iff_ne_zero.2 hz0)
    exact absurd hE (not_lt.2 this)
  refine ⟨h1a, hg, ?_, hlt2, hval⟩
  by_contra hc
  push Not at hc
  have : E ≤ Om (1 + 1) := by
    rw [← hval]
    calc veblen (invVeblen₁ E) (invVeblen₂ E) ≤ veblen (invVeblen₁ E) (Om (1 + 1)) :=
          (veblen_le_veblen_iff_right).2 hc
      _ = Om (1 + 1) := ldOm2_SC.veblen_right hg
  exact absurd hΩE (not_lt.2 this)

/-- **The level of a node is a member** (of every closure containing the node), **and a code below `Q`** (of every
code set over `Ω₂` containing the node). -/
theorem tdNode_lev {A B a y Q : Ordinal.{0}} (haE : a < veblen a y) (hlt : y < veblen a y) :
    (veblen a y ∈ S.CSet A B → a ∈ S.CSet A B ∧ y ∈ S.CSet A B) ∧
    (SC Q → LeCl (Om (1 + 1)) Q (veblen a y) → a < Om (1 + 1) → LeCl (Om (1 + 1)) Q a ∧ a < Q) :=
  ⟨fun h => mem_of_veblen_mem h haE hlt, fun hQ h haW => by
    have hcl := tdCl_lev ldOm2_SC _ h a y rfl hlt
    exact ⟨hcl, tdCl_lt hQ a hcl haW⟩⟩

/-! ## The image with the levels read by `Θ` -/

/-- **The image of a term with the levels read by `Θ`**: `φ(a, Ω₂ + Y) ↦ φ(Θ a, Ω₁ + Ŷ)`. -/
noncomputable def tdIL (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaT → Ordinal.{0}
  | .zero => 0
  | .phi a Y => veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l Y)
  | .term P R c => tdIL S l P + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c

/-- **The image `Θ̂_L E`** of the normal-form term, with the levels read by `Θ`. -/
noncomputable def tdThL (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} := tdIL S l (taTm E)

section Read

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- `Θ a = a` for `a < ρ_λ`: **the levels below `ρ_λ` are kept.** -/
theorem tdThL_lev {a : Ordinal.{0}} (ha : a < upsilon l) : gxTh (upsilon l) (ldAtR S l) a = a := gxTh_small ha.le

/-- **On well-formed terms (levels below `K`) the two images agree.** -/
theorem tdIL_eq : ∀ t : TaT, TdWF S l t → tdIL S l t = taI S l t
  | .zero, _ => rfl
  | .phi a Y, ⟨ha, hY, _, _⟩ => by
    show veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l Y) = veblen a (Om 1 + taI S l Y)
    rw [tdThL_lev (ha.2.trans_le (tdK_le_rho hl hX)), tdIL_eq Y hY]
  | .term P R c, ⟨hP, hR, _⟩ => by
    show tdIL S l P + leOe (tdIL S l R) * _ = taI S l P + leOe (taI S l R) * _
    rw [tdIL_eq P hP, tdIL_eq R hR]

/-- **`Θ̂_L = Ta.taTh` below `φ(K, Ω₂ + 1)`** (on `H_λ`). -/
theorem tdThL_eq {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE : E < tdTop S) : tdThL S l E = taTh S l E :=
  tdIL_eq hl hX _ (tdTm_spec hl hX E hEH hE).1

omit hl hX in
/-- **THE φ LAW WITH THE LEVEL READ**: `Θ̂_L(φ(a, Ω₂ + y)) = φ(Θ a, Ω₁ + Θ̂_L y)` at a node. -/
theorem tdThL_node {E : Ordinal.{0}} (h0 : ¬ (0 < E ∧ sgLW E < E))
    (h : Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E) :
    tdThL S l E = veblen (gxTh (upsilon l) (ldAtR S l) (invVeblen₁ E))
      (Om 1 + tdThL S l (invVeblen₂ E - Om (1 + 1))) := by
  unfold tdThL; rw [taTm_node h0 h]; rfl

end Read

/-! ## The node with a code level: the φ law and the move -/

/-- **THE φ LAW WITH THE LEVEL READ**: `Θ̂_L(φ(a, Ω₂ + z)) = φ(Θ a, Ω₁ + Θ̂_L z)` off the fixed points. -/
theorem tdThL_veb {l a z : Ordinal.{0}} (ha0 : a ≠ 0) (hz : 1 ≤ z)
    (hlt : Om (1 + 1) + z < veblen a (Om (1 + 1) + z)) :
    tdThL S l (veblen a (Om (1 + 1) + z)) = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z) := by
  have hW := taWe_veb ha0 hz
  have hc : ¬ (0 < veblen a (Om (1 + 1) + z) ∧ sgLW (veblen a (Om (1 + 1) + z)) < veblen a (Om (1 + 1) + z)) := by
    rintro ⟨-, h⟩
    conv_lhs at h => rw [← hW]
    rw [taSgLW_We] at h
    exact lt_irrefl _ h
  have h1 : invVeblen₁ (veblen a (Om (1 + 1) + z)) = a := invVeblen₁_veblen hlt
  have h2 : invVeblen₂ (veblen a (Om (1 + 1) + z)) = Om (1 + 1) + z := invVeblen₂_veblen ha0 hlt
  have hΩ : Om (1 + 1) < Om (1 + 1) + z := lt_add_of_pos_right _ (zero_lt_one.trans_le hz)
  rw [tdThL_node hc (by rw [h2]; exact ⟨hΩ, hlt⟩), h1, h2, Ordinal.add_sub_cancel]

/-- **THE MOVE OF A NODE WITH A CODE LEVEL**: for `E = φ(a, Ω₂ + z)` off the fixed points, with the level `a`
and the argument `z` moved (`Θ'(B_n a) = B_n(Θ a)`, `Θ̂'_L(B_n z) = B_n(Θ̂_L z)`) and the image node
`φ(Θ a, Ω₁ + Θ̂_L z)` off its fixed points: `B_n E = φ(B_n a, Ω₂ + B_n z)` (again a node off its fixed points)
and **`Θ̂'_L(B_n E) = B_n(Θ̂_L E)`**. -/
theorem tdB_nodeL {n : ℕ} {l l' a z : Ordinal.{0}} (hDa : MvD S a) (hDz : MvD S z) (ha1 : 1 ≤ a)
    (haW : a < Om (1 + 1)) (hz1 : 1 ≤ z) (hlt : Om (1 + 1) + z < veblen a (Om (1 + 1) + z))
    (hDΘa : MvD S (gxTh (upsilon l) (ldAtR S l) a)) (hΘaO : gxTh (upsilon l) (ldAtR S l) a < Om 1)
    (hDΘz : MvD S (tdThL S l z))
    (hlth : Om 1 + tdThL S l z < veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z))
    (hBa : gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n a) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) a))
    (hBz : tdThL S l' (Bc.bcB S n z) = Bc.bcB S n (tdThL S l z)) :
    MvD S (veblen a (Om (1 + 1) + z)) ∧
      Bc.bcB S n (veblen a (Om (1 + 1) + z)) = veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) ∧
      Om (1 + 1) + Bc.bcB S n z < veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) ∧
      tdThL S l' (Bc.bcB S n (veblen a (Om (1 + 1) + z))) =
        Bc.bcB S n (tdThL S l (veblen a (Om (1 + 1) + z))) := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDy, hBy⟩ := mvB_add (k := n) hD2 hDz
  rw [hB2] at hBy
  have hay : a < Om (1 + 1) + z := haW.trans_le le_self_add
  obtain ⟨hDE, hBE⟩ := mwB_phi (k := n) hDa hDy (hay.trans hlt) hlt
  rw [hBy] at hBE
  have hBlt : Om (1 + 1) + Bc.bcB S n z < veblen (Bc.bcB S n a) (Om (1 + 1) + Bc.bcB S n z) := by
    have := (mvB_lt_iff (k := n) hDy hDE).2 hlt
    rwa [hBy, hBE] at this
  have hBa1 : 1 ≤ Bc.bcB S n a := by have := leB_le (n := n) hD1 hDa ha1; rwa [mwB_one] at this
  have hBz1 : 1 ≤ Bc.bcB S n z := by have := leB_le (n := n) hD1 hDz hz1; rwa [mwB_one] at this
  refine ⟨hDE, hBE, hBlt, ?_⟩
  -- the image side
  obtain ⟨hDb, hBb⟩ := mvB_add (k := n) hDO hDΘz
  rw [hBO] at hBb
  have hΘab : gxTh (upsilon l) (ldAtR S l) a < Om 1 + tdThL S l z := hΘaO.trans_le le_self_add
  obtain ⟨-, hBΘE⟩ := mwB_phi (k := n) hDΘa hDb (hΘab.trans hlth) hlth
  rw [hBb] at hBΘE
  rw [hBE, tdThL_veb (l := l') (zero_lt_one.trans_le hBa1).ne' hBz1 hBlt, hBa, hBz, tdThL_veb ha0 hz1 hlt, hBΘE]

end Googology.Trans.PoR.InaccPsi.R2.Td
