import Googology.Trans.PoR.InaccPsi.R2.GiWp

/-!
# THE LAST TERM OF A LIMIT CODE BELOW `ε_{Ω₁+1}^ω`; the reading system `gwRS`

For a limit code `c = E^k·d + r ∈ (ε_{Ω₁+1}, ε_{Ω₁+1}^ω)` (`E = ε_{Ω₁+1}`) the reading `c(x) = ε_{x+1}^k·d(x) + r(x)` is
`l'(x) + ω^{logend}` with Lemma IMG for the logend (`GiLD` of `R2.GiRS`), by induction on the code:

* `r` a limit below `E`: `logend = logend(r(x))` (the term `tlg`, Lemma IMG `pkg_ot`);
* `r = E`: `logend = ε_{x+1}` (`pkg_eN`);
* `r > E` a limit: the last term of `r` (induction), the copies keep the gate of `r` (`gi_pkg_weaken`);
* `r = 0`, `d = d' + 1`: `logend = ε_{x+1}·k` (`pkg_eNm`);
* `r = 0`, `d` a limit: `logend = ε_{x+1}·k + logend(d(x))` (`pkg_eMt`).

* `gi_pkg_weaken`, `gw_dvd`, `gwLD_ne` (**the data exists at every limit code in `(ε_{Ω₁+1}, ε_{Ω₁+1}^ω)`**);
* `gwRS` (**THE READING SYSTEM of the codes below `ε_{Ω₁+1}^ω`**, cofinal codes `ε_{Ω₁+1}^{k+1}`, gate `0`).

No new axiom.  New definition: `gwRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gb

/-- A package for the copies that keep a smaller gate `g' < ρ` is one for the copies that keep `g` (put `g'` into the
witness set). -/
theorem gi_pkg_weaken {g g' ρ δ : Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (h : GhPkg g' ρ δ T) (hg' : g' < ρ) :
    GhPkg g ρ δ T := by
  classical
  obtain ⟨W, Z, w, hm, hI⟩ := h
  refine ⟨W, insert g' Z, w.insZ hg', Finset.union_subset_union (subset_refl W) (Finset.subset_insert _ _) hm,
    fun A f hW hZ C => hI A f hW (fun z hz => hZ (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_coe.1 hz)))) ⟨C.toImgCtx, hZ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))⟩⟩

theorem gw_dvd {x e k q : Ordinal.{0}} (he : e ≤ eN x * k) : ω ^ e ∣ eN x ^ k * q := by
  rw [gw_eNpow]
  exact dvd_trans (opow_dvd_opow ω he) (dvd_mul_right _ _)

theorem gw_one_le_k {k : Ordinal.{0}} (hk : k ≠ 0) (x : Ordinal.{0}) : eN x ≤ eN x * k :=
  le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hk)

/-- **The data `GiLD` exists at every limit code `c ∈ (ε_{Ω₁+1}, ε_{Ω₁+1}^ω)`.** -/
theorem gwLD_ne : ∀ c, IsSuccLimit c → gfE < c → c < gwB → Nonempty (GiLD gwK gwR c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hl hEc hc
  have hcE : gfE ≤ c := hEc.le
  obtain ⟨hk, hd0, hdE, hr, hdec⟩ := gw_parts hcE
  obtain ⟨n0, hn0⟩ := gw_nat_of_lt hc hcE
  obtain ⟨n, hn⟩ : ∃ n : ℕ, log gfE c = ((n + 1 : ℕ) : Ordinal.{0}) := by
    obtain ⟨m, rfl⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by
      have : n0 ≠ 0 := by rintro rfl; exact hk (by rw [hn0, Nat.cast_zero])
      omega⟩
    exact ⟨m, hn0⟩
  set k := log gfE c with hkdef
  set d := c / gfE ^ k with hddef
  set r := c % gfE ^ k with hrdef
  have hrc : r < c := mod_opow_log_lt_self gfE (gw_ne_of_le hcE)
  have hgc : gwG c = max (giQ d) (gwG r) := gwG_dec hcE
  have hRc : ∀ x, gwR c x = eN x ^ k * rdc d x + gwR r x := fun x => gwR_dec hcE x
  have hgK : ∀ b, gwK.gt b = gwG b := fun _ => rfl
  have hEk : gfE ≤ gfE ^ k := by
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ k := opow_le_opow_right eW_E.pos (one_le_iff_ne_zero.2 hk)
  have hcp_ge : ∀ b, b ≠ 0 → gfE ≤ gfE ^ k * b := fun b hb =>
    hEk.trans (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hb))
  have hRp : ∀ b t x, b ≠ 0 → b < gfE → t < gfE ^ k → gwR (gfE ^ k * b + t) x = eN x ^ k * rdc b x + gwR t x :=
    fun b t x hb hbE ht => gwR_cnf hk hb hbE ht x
  have hGp : ∀ b t, b ≠ 0 → b < gfE → t < gfE ^ k → gwG (gfE ^ k * b + t) = max (giQ b) (gwG t) :=
    fun b t hb hbE ht => gwG_cnf hk hb hbE ht
  have hk0 : (0 : Ordinal.{0}) < gfE ^ k := opow_pos _ eW_E.pos
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `r = 0`: `c = E^k·d`
    have hRc0 : ∀ x, gwR c x = eN x ^ k * rdc d x := fun x => by
      rw [hRc, hr0, gwR_low eW_E.pos, rdc_zero, add_zero]
    have hgc0 : gwG c = giQ d := by rw [hgc, hr0, gwG_zero, max_eq_left zero_le]
    have hcd : c = gfE ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hsucc⟩ | hdl
    · exact absurd h0 hd0
    · -- `d = d' + 1`
      rw [succ_eq_add_one] at hsucc
      have hd'E : d' < gfE := (lt_add_one d').trans (by rw [hsucc]; exact hdE)
      have hRs : ∀ x, gwR c x = eN x ^ k * rdc d' x + ω ^ (eN x * k) := fun x => by
        rw [hRc0, ← hsucc, (rdc_succ d' hd'E x).1, mul_add_one, gw_eNpow]
      have hlg : ∀ x, lg (gwR c x) = eN x * k := fun x => by
        rw [hRs]; exact Ge.lg_add_opow (gw_dvd le_rfl)
      refine ⟨{
        cp := if d' = 0 then gfE else gfE ^ k * d' + 0
        lp := (fun x => eN x ^ k * rdc d' x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · split_ifs with h0
        · exact le_rfl
        · rw [add_zero]; exact hcp_ge d' h0
      · split_ifs with h0
        · exact hEc
        · rw [hcd, add_zero, ← hsucc]
          exact (mul_lt_mul_iff_right₀ hk0).2 (lt_add_one d')
      · split_ifs with h0
        · rw [gwG_E]; exact zero_le
        · rw [hGp d' 0 h0 hd'E hk0, gwG_zero, max_eq_left zero_le, hgc0, ← hsucc]
          unfold giQ
          by_cases h1 : d' < ω
          · rw [if_pos h1]; exact zero_le
          · rw [if_neg h1, if_neg (fun h => h1 ((lt_add_one d').trans h))]; exact (rdc_succ d' hd'E 0).2.1
      · intro x _ _ _
        refine ⟨by rw [hlg x]; exact hRs x, by rw [hlg x]; exact gw_dvd le_rfl,
          by rw [hlg x]; exact (mul_pos (eN_E x).pos (pos_iff_ne_zero.2 hk)).ne', ?_⟩
        split_ifs with h0
        · rw [h0, rdc_zero, mul_zero]; exact zero_le
        · rw [hRp d' 0 x h0 hd'E hk0, gwR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        refine GhPkg.congr h (GhPkg.of_img (h.pkg_eNm n)) (fun y _ _ _ => ?_) hg
        rw [hlg y, hn]
    · -- `d` a limit
      obtain ⟨d'', l, dd, hd''d, hg'', hgl, hdd, -, hF⟩ := rdc_lim_facts hdl hdE
      have hdω : ω ≤ d := Ordinal.le_of_dvd hd0 ((isSuccLimit_iff_omega0_dvd.1 hdl).2)
      have hQd : giQ d = gtc d := by unfold giQ; rw [if_neg (not_lt.2 hdω)]
      have hgd : ∀ x, gwG c < x → gtc d < x := fun x h => by rw [hgc0, hQd] at h; exact h
      have hd''E : d'' < gfE := hd''d.trans hdE
      have hdec2 : ∀ x, InE x → gtc d < x →
          gwR c x = eN x ^ k * rdc d'' x + ω ^ (eN x * k + OT.ev (tlg l dd) x) ∧
            ω ^ (eN x * k + OT.ev (tlg l dd) x) ∣ eN x ^ k * rdc d'' x ∧
            lg (gwR c x) = eN x * k + OT.ev (tlg l dd) x := by
        intro x hx hgx
        obtain ⟨e1, e2, e3, -, -, -⟩ := hF x hx hgx
        have h1 : gwR c x = eN x ^ k * rdc d'' x + ω ^ (eN x * k + OT.ev (tlg l dd) x) := by
          rw [hRc0, e1, mul_add, gw_eNpow, ← opow_add, e3]
        have h2 : ω ^ (eN x * k + OT.ev (tlg l dd) x) ∣ eN x ^ k * rdc d'' x := by
          rw [e3] at e2
          obtain ⟨m, hm⟩ := e2
          exact ⟨m, by rw [hm, ← mul_assoc, gw_eNpow, ← opow_add]⟩
        exact ⟨h1, h2, by rw [h1]; exact Ge.lg_add_opow h2⟩
      refine ⟨{
        cp := if d'' = 0 then gfE else gfE ^ k * d'' + 0
        lp := (fun x => eN x ^ k * rdc d'' x)
        cp_ge := ?_
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · split_ifs with h0
        · exact le_rfl
        · rw [add_zero]; exact hcp_ge d'' h0
      · split_ifs with h0
        · exact hEc
        · rw [hcd, add_zero]
          exact (mul_lt_mul_iff_right₀ hk0).2 hd''d
      · split_ifs with h0
        · rw [gwG_E]; exact zero_le
        · rw [hGp d'' 0 h0 hd''E hk0, gwG_zero, max_eq_left zero_le, hgc0, hQd]
          exact (giQ_le d'').trans hg''
      · intro x hx _ hgx
        obtain ⟨h1, h2, h3⟩ := hdec2 x hx (hgd x hgx)
        refine ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact (add_pos_of_pos_of_nonneg
          (mul_pos (eN_E x).pos (pos_iff_ne_zero.2 hk)) zero_le).ne', ?_⟩
        split_ifs with h0
        · rw [h0, rdc_zero, mul_zero]; exact zero_le
        · rw [hRp d'' 0 x h0 hd''E hk0, gwR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        have hgρ := hgd ρ hg
        obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hgρ
        have hcb : OT.CB (tlg l dd) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) (hdd.trans_lt hgρ)
        have h1 : 1 ≤ OT.ev (tlg l dd) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
        refine GhPkg.congr h (GhPkg.of_img (h.pkg_eMt n hcb h1)) (fun y hyE _ hgy => ?_) hg
        rw [(hdec2 y hyE (hgd y hgy)).2.2, hn]
  · -- `r ≠ 0`: `r` a limit
    have hrl : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hsucc⟩ | hrl
      · exact absurd h0 hr0
      · exfalso
        rw [succ_eq_add_one] at hsucc
        have e : c = succ (gfE ^ k * d + r') := by rw [← hdec, ← hsucc, ← add_assoc, succ_eq_add_one]
        rw [e] at hl
        exact Order.not_isSuccLimit_succ _ hl
      · exact hrl
    have hgr : ∀ x, gwG c < x → gwG r < x := fun x h => (le_max_right _ _).trans_lt (hgc ▸ h)
    -- the logend of `r(x)` lies below `ε_{x+1}·k`
    have hlgk : ∀ x, InE x → gwG r < x → lg (gwR r x) ≤ eN x * k := by
      intro x hx hgx
      have hb := gwR_bound hx r hgx k hk hr
      rw [gw_eNpow] at hb
      have h0 : gwR r x ≠ 0 := by
        rcases lt_or_ge r gfE with hrE' | hrE'
        · rw [gwR_low hrE']; exact (rdc_pos hx hr0 hrE').ne'
        · exact (lt_of_lt_of_le (opow_pos _ (eN_E x).pos) (gw_lead_le hx hrE')).ne'
      have h1 : ω ^ lg (gwR r x) ≤ gwR r x := Ordinal.le_of_dvd h0 (lg_dvd h0)
      exact ((opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hb)).le
    rcases lt_or_ge r gfE with hrE | hrE
    · -- `r` a limit below `E`
      obtain ⟨r', l, dd, hr'r, hgr', hgl, hdd, -, hF⟩ := rdc_lim_facts hrl hrE
      have hr'E : r' < gfE := hr'r.trans hrE
      have hr'k : r' < gfE ^ k := hr'E.trans_le hEk
      have hga : ∀ x, gwG c < x → gtc r < x := fun x h => by rw [← gwG_low hrE]; exact hgr x h
      have hdec2 : ∀ x, InE x → gtc r < x →
          gwR c x = (eN x ^ k * rdc d x + rdc r' x) + ω ^ lg (rdc r x) ∧
            ω ^ lg (rdc r x) ∣ eN x ^ k * rdc d x + rdc r' x ∧ lg (gwR c x) = lg (rdc r x) ∧ lg (rdc r x) ≠ 0 := by
        intro x hx hgx
        obtain ⟨e1, e2, -, hω, -, e6⟩ := hF x hx hgx
        have hne : rdc r x ≠ 0 := (omega0_pos.trans_le hω).ne'
        have hle : lg (rdc r x) ≤ eN x * k :=
          ((lg_le hne).trans (rdc_lt_eN hx r hgx).le).trans (gw_one_le_k hk x)
        have hdv : ω ^ lg (rdc r x) ∣ eN x ^ k * rdc d x + rdc r' x := Ge.dvd_add' (gw_dvd hle) e2
        have hsum : gwR c x = (eN x ^ k * rdc d x + rdc r' x) + ω ^ lg (rdc r x) := by
          rw [hRc, gwR_low hrE, add_assoc, ← e1]
        exact ⟨hsum, hdv, by rw [hsum]; exact Ge.lg_add_opow hdv, (Gc.gc_lg_pos e6).ne'⟩
      refine ⟨{
        cp := gfE ^ k * d + r'
        lp := (fun x => eN x ^ k * rdc d x + rdc r' x)
        cp_ge := (hcp_ge d hd0).trans le_self_add
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 hr'r
      · rw [hGp d r' hd0 hdE hr'k, gwG_low hr'E, hgc, gwG_low hrE]; exact max_le_max le_rfl hgr'
      · intro x hx _ hgx
        obtain ⟨h1, h2, h3, h4⟩ := hdec2 x hx (hga x hgx)
        exact ⟨by rw [h3]; exact h1, by rw [h3]; exact h2, by rw [h3]; exact h4,
          by rw [hRp d r' x hd0 hdE hr'k, gwR_low hr'E]⟩
      · intro ρ τ δ h hg
        have hρE := upsPt_inE h.ρU
        have hgρ := hga ρ hg
        obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hgρ
        have hcb : OT.CB (tlg l dd) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) (hdd.trans_lt hgρ)
        have h1 : 1 ≤ OT.ev (tlg l dd) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
        refine GhPkg.congr h (GhPkg.of_img (h.pkg_ot hcb h1)) (fun y hyE _ hgy => ?_) hg
        obtain ⟨-, -, f3, -, -, -⟩ := hF y hyE (hga y hgy)
        rw [(hdec2 y hyE (hga y hgy)).2.2.1, f3]
    rcases hrE.lt_or_eq with hEr | hEr
    · -- `r > E` a limit: the last term of `r`
      obtain ⟨D⟩ := IH r hrc hrl hEr (hrc.trans hc)
      have hDk : D.cp < gfE ^ k := D.cp_lt.trans hr
      have hlgc : ∀ x, InE x → x < Om1 → gwG c < x → lg (gwR c x) = lg (gwR r x) ∧
          ω ^ lg (gwR r x) ∣ eN x ^ k * rdc d x + D.lp x ∧
          gwR c x = (eN x ^ k * rdc d x + D.lp x) + ω ^ lg (gwR r x) := by
        intro x hx hx1 hgx
        obtain ⟨e1, e2, -, -⟩ := D.dec x hx hx1 (hgr x hgx)
        have hdv : ω ^ lg (gwR r x) ∣ eN x ^ k * rdc d x + D.lp x :=
          Ge.dvd_add' (gw_dvd (hlgk x hx (hgr x hgx))) e2
        have hsum : gwR c x = (eN x ^ k * rdc d x + D.lp x) + ω ^ lg (gwR r x) := by
          rw [hRc, add_assoc, ← e1]
        exact ⟨by rw [hsum]; exact Ge.lg_add_opow hdv, hdv, hsum⟩
      refine ⟨{
        cp := gfE ^ k * d + D.cp
        lp := (fun x => eN x ^ k * rdc d x + D.lp x)
        cp_ge := (hcp_ge d hd0).trans le_self_add
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 D.cp_lt
      · rw [hGp d D.cp hd0 hdE hDk, hgc]; exact max_le_max le_rfl D.cp_g
      · intro x hx hx1 hgx
        obtain ⟨h1, h2, h3⟩ := hlgc x hx hx1 hgx
        obtain ⟨-, -, e3, e4⟩ := D.dec x hx hx1 (hgr x hgx)
        refine ⟨by rw [h1]; exact h3, by rw [h1]; exact h2, by rw [h1]; exact e3, ?_⟩
        rw [hRp d D.cp x hd0 hdE hDk]
        exact add_le_add le_rfl e4
      · intro ρ τ δ h hg
        have hgρ := hgr ρ hg
        refine GhPkg.congr h (gi_pkg_weaken (D.pkg ρ τ δ h hgρ) hgρ) (fun y hyE hy1 hgy => ?_) hg
        exact ((hlgc y hyE hy1 hgy).1).symm
    · -- `r = E`
      have hRE : ∀ x, gwR c x = eN x ^ k * rdc d x + ω ^ eN x := fun x => by
        rw [hRc, ← hEr, gwR_E, show ω ^ eN x = eN x from eN_E x]
      have hlg : ∀ x, lg (gwR c x) = eN x := fun x => by
        rw [hRE]; exact Ge.lg_add_opow (gw_dvd (gw_one_le_k hk x))
      refine ⟨{
        cp := gfE ^ k * d + 0
        lp := (fun x => eN x ^ k * rdc d x)
        cp_ge := by rw [add_zero]; exact hcp_ge d hd0
        cp_lt := ?_
        cp_g := ?_
        dec := ?_
        pkg := ?_ }⟩
      all_goals try simp only [hgK]
      · rw [← hdec, ← hEr]; exact (add_lt_add_iff_left _).2 eW_E.pos
      · rw [hGp d 0 hd0 hdE hk0, hgc, gwG_zero, ← hEr, gwG_E]
      · intro x _ _ _
        refine ⟨by rw [hlg x]; exact hRE x, by rw [hlg x]; exact gw_dvd (gw_one_le_k hk x),
          by rw [hlg x]; exact (eN_E x).pos.ne', ?_⟩
        rw [hRp d 0 x hd0 hdE hk0, gwR_low eW_E.pos, rdc_zero, add_zero]
      · intro ρ τ δ h hg
        exact GhPkg.congr h (GhPkg.of_img h.pkg_eN) (fun y _ _ _ => (hlg y).symm) hg

end Googology.Trans.PoR.InaccPsi.R2.Gi
