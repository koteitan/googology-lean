import Googology.Trans.PoR.InaccPsi.R2.GhEps

/-!
# ONE GENERIC RECURSION FOR THE CODES `ε_{Ω₁+1}·(n+1) + a` (`n < ω`, `a < ε_{Ω₁+1}`): layers with top
`Γ_{x+1+ε_{x+1}·(n+1)+a(x)}`

The codes `c` with `ε_{Ω₁+1} ≤ c < ε_{Ω₁+1}·ω` are `c = ε_{Ω₁+1}·(n+1) + a`, `a < ε_{Ω₁+1}` (`R2.GfSub`), read with
`Ω₁ ↦ x` as `ε_{x+1}·(n+1) + a(x)`, gate `gtc a`.  One recursion on the pair `(n, a)`:

* the start of the shift `n` (`GhStart n`, the code `ε_{Ω₁+1}·(n+1)`): `n = 0` is `R2.GhEps.ghEB`; `n + 1` is the union
  step (`R2.GhU`) over all layers of the shift `n`, offset `ε_{x+1}·(n+2)`, logend `ε_{x+1}` (Lemma IMG `pkg_eN`);
* the successor `a + 1`: the gated ladder over the layer of `a` with the term offset `ε_{x+1}·(n+1) + a(x) + 1`
  (`Ge.geqLimB`, Lemma EXACT from `gh_eNm_pi`, `Gf.rdc_pi`, `pi_add`);
* the limit `a`: the union step with offset `ε_{x+1}·(n+1) + a(x)`, logend `logend(a(x))` (the term `tlg l d`, Lemma
  IMG `pkg_ot`), predecessor `a'` (`Gf.rdc_lim_facts`).

* `ghBs`, `ghBs_lt`, `ghBs_pi`, `ghBs_dvd`, `ghBs_succ`, `ghO_lt`, `gh_lg_shift`;
* `GhStart`, `GhSt`, `ghSt0`, `ghH_succ`, `ghStSucc`, `ghFL`, `ghStLim`, `ghRec`, `ghFN`, `ghStartNext`, `ghS`;
* `ghB n a` (**THE GATED LAYER OF THE CODE `ε_{Ω₁+1}·(n+1) + a`**), `ghB_spec` (**the generic theorem**: gate `gtc a`,
  top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}·(n+1) + a(x)) = Γ_{x+1+ε_{x+1}·(n+1)+a(x)}` at every `ε`-number base above the gate).

No new axiom.  New definitions: `ghBs`, `GhStart`, `GhSt`, `ghSt0`, `ghStSucc`, `ghFL`, `ghStLim`, `ghRec`, `ghFN`,
`ghStartNext`, `ghS`, `ghB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf

/-! ## The shift `ε_{x+1}·(n+1)` -/

/-- **The shift** `ε_{x+1}·(n+1)`. -/
noncomputable def ghBs (n : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := eN x * ((n + 1 : ℕ) : Ordinal.{0})

theorem ghBs_zero (x : Ordinal.{0}) : ghBs 0 x = eN x := by simp [ghBs]

theorem ghBs_succ (n : ℕ) (x : Ordinal.{0}) : ghBs (n + 1) x = ghBs n x + eN x := by
  unfold ghBs; rw [Nat.cast_succ (n + 1), mul_add_one]

theorem ghBs_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) : ghBs n x < gq 0 x :=
  gh_eNm_lt_gq0 hx hx1 (n + 1)

theorem ghBs_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) :
    ghBs n ρ ∈ TB ρ σ ∧ pi σ ρ (ghBs n ρ) = ghBs n σ := gh_eNm_pi hB (n + 1)

theorem ghBs_dvd {x e : Ordinal.{0}} (he : e ≤ eN x) (n : ℕ) : ω ^ e ∣ ghBs n x := by
  have h1 : ω ^ e ∣ eN x := by
    rw [← show ω ^ eN x = eN x from eN_E x]; exact opow_dvd_opow ω he
  exact dvd_trans h1 (dvd_mul_right _ _)

theorem ghO_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) (a : Ordinal.{0}) (hg : gtc a < x) :
    ghBs n x + rdc a x < gq 0 x :=
  (inE_indec (gfq0_facts hx hx1).2.2.2).add_lt (ghBs_lt hx hx1 n)
    ((rdc_lt_eN hx a hg).trans (gh_eN_lt_gq0 hx hx1))

theorem ghO1_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) (a : Ordinal.{0}) (hg : gtc a < x) :
    ghBs n x + rdc a x + 1 < gq 0 x :=
  (inE_indec (gfq0_facts hx hx1).2.2.2).add_lt (ghO_lt hx hx1 n a hg)
    (one_lt_omega0.trans (omega0_lt_inE (gfq0_facts hx hx1).2.2.2))

/-- The last term of a shifted limit code: `logend(ε_{x+1}·(n+1) + a(x)) = logend(a(x))`, with the decomposition. -/
theorem gh_lg_shift {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    ∃ a', a' < a ∧ gtc a' ≤ gtc a ∧ ∀ (n : ℕ) (x : Ordinal.{0}), InE x → gtc a < x →
      ghBs n x + rdc a x = ghBs n x + rdc a' x + ω ^ lg (ghBs n x + rdc a x) ∧
        ω ^ lg (ghBs n x + rdc a x) ∣ ghBs n x + rdc a' x ∧ lg (ghBs n x + rdc a x) = lg (rdc a x) := by
  obtain ⟨a', l, d, ha'a, hg', -, -, -, hF⟩ := rdc_lim_facts hl ha
  refine ⟨a', ha'a, hg', fun n x hx hgx => ?_⟩
  obtain ⟨e1, e2, -, hω, -, -⟩ := hF x hx hgx
  have hne : rdc a x ≠ 0 := (lt_of_lt_of_le omega0_pos hω).ne'
  have hle : lg (rdc a x) ≤ eN x := (lg_le hne).trans (rdc_lt_eN hx a hgx).le
  have hd : ω ^ lg (rdc a x) ∣ ghBs n x + rdc a' x := Ge.dvd_add' (ghBs_dvd hle n) e2
  have hsum : ghBs n x + rdc a x = ghBs n x + rdc a' x + ω ^ lg (rdc a x) := by
    conv_lhs => rw [e1]
    rw [add_assoc]
  have hlg : lg (ghBs n x + rdc a x) = lg (rdc a x) := by rw [hsum]; exact Ge.lg_add_opow hd
  rw [hlg]
  exact ⟨hsum, hd, rfl⟩

/-! ## The recursion -/

/-- **The start of the shift `n`** (the code `ε_{Ω₁+1}·(n+1)`): a gate-`0` layer with top
`ϑˣ(Ω₁·Ω₁ + ε_{x+1}·(n+1))`. -/
def GhStart (n : ℕ) : Type 2 :=
  {B : GdB // B.g = 0 ∧ ∀ x, InE x → x < Om1 → B.K.E x = gq (ghBs n x) x}

/-- **The value at the code `ε_{Ω₁+1}·(n+1) + a`**: a gated layer with gate `gtc a` and top
`ϑˣ(Ω₁·Ω₁ + ε_{x+1}·(n+1) + a(x))` above the gate. -/
def GhSt (n : ℕ) (a : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = gtc a ∧ ∀ x, InE x → x < Om1 → gtc a < x → B.K.E x = gq (ghBs n x + rdc a x) x}

def ghSt0 {n : ℕ} (s : GhStart n) : GhSt n 0 :=
  ⟨s.1, by rw [s.2.1, gtc_zero], fun x hx hx1 _ => by rw [s.2.2 x hx hx1, rdc_zero, add_zero]⟩

/-- **The term-offset limit hypothesis for the successor**: over the layer of `a`, the offset
`ε_{x+1}·(n+1) + a(x) + 1`. -/
theorem ghH_succ {n : ℕ} {a : Ordinal.{0}} (s : GhSt n a) (ha : a + 1 < gfE) :
    GeqH s.1 (fun x => ghBs n x + rdc a x + 1) := by
  have ha' : a < gfE := (lt_add_one a).trans ha
  refine ⟨fun x hx hx1 hg => ?_, fun x hx hx1 hg => ?_, fun x hx hx1 hg j _ hj => ?_, fun x hx hx1 hg => ?_,
    fun σ ρ hB hg => ?_⟩
  · rw [s.2.1] at hg; exact gfq_T hx hx1 (ghO1_lt hx hx1 n a hg)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    obtain ⟨hT, h1⟩ := gfq_T hx hx1 (ghO_lt hx hx1 n a hg)
    exact (ghO1_lt hx hx1 n a hg).trans_le (gfq0_le hx hx1 hT h1)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gfq_mono hx hx1 (ghO_lt hx hx1 n a hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gfq_lt hx hx1 (ghO1_lt hx hx1 n a hg) (lt_add_one _)
  · rw [s.2.1] at hg
    have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
    obtain ⟨h1, h2⟩ := ghBs_pi hB n
    obtain ⟨h3, h4⟩ := rdc_pi hB ha' hg
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    obtain ⟨h7, h8⟩ := pi_add hB h5 (mem_TB_of_lt hB h1σ)
    exact ⟨h7, by rw [h8, h6, h2, h4, pi_lt hB h1σ]⟩

theorem gh_g_succ {n : ℕ} {a : Ordinal.{0}} (s : GhSt n a) (ha : a + 1 < gfE) :
    (geqLimB s.1 (fun x => ghBs n x + rdc a x + 1) (ghH_succ s ha)).g ≤ gtc (a + 1) := by
  rw [geqLimB_g, s.2.1]; exact (rdc_succ a ((lt_add_one a).trans ha) 0).2.1

/-- The successor step: the limit of the gated ladder over the layer of `a`. -/
noncomputable def ghStSucc (n : ℕ) (a : Ordinal.{0}) (s : GhSt n a) (ha : a + 1 < gfE) : GhSt n (a + 1) :=
  ⟨(geqLimB s.1 (fun x => ghBs n x + rdc a x + 1) (ghH_succ s ha)).mono (gh_g_succ s ha), rfl, fun x _ _ _ => by
    show gq (ghBs n x + rdc a x + 1) x = gq (ghBs n x + rdc (a + 1) x) x
    rw [(rdc_succ a ((lt_add_one a).trans ha) x).1, add_assoc]⟩

/-- **The data of the union at a shifted limit code** `ε_{Ω₁+1}·(n+1) + a`. -/
noncomputable def ghFL (n : ℕ) (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (IH : ∀ b < a, GhSt n b) :
    GhUF (gtc a) where
  I := Iio a
  K := fun b => (IH b.1 b.2).1
  gi := fun b => gtc b.1
  o := fun b x => ghBs n x + rdc b.1 x
  l := fun x => ghBs n x + rdc a x
  lp := fun x => ghBs n x + rdc (gh_lg_shift hl ha).choose x
  i0 := ⟨0, hl.bot_lt⟩
  ip := ⟨(gh_lg_shift hl ha).choose, (gh_lg_shift hl ha).choose_spec.1⟩
  g_le := fun b => (IH b.1 b.2).2.1.le
  gi0 := gtc_zero
  gip := (gh_lg_shift hl ha).choose_spec.2.1
  E_eq := fun b x hx hx1 hg => (IH b.1 b.2).2.2 x hx hx1 hg
  o_lt := fun b x hx _ hg hgb => (add_lt_add_iff_left _).2 (rdc_mono hx ha b.2 hg hgb)
  l_lt := fun x hx hx1 hg => ghO_lt hx hx1 n a hg
  lim := fun x hx _ hg => by
    obtain ⟨_, _, _, _, _, _, _, _, hF⟩ := rdc_lim_facts hl ha
    exact isSuccLimit_add _ (hF x hx hg).2.2.2.2.2
  cof := fun x hx hx1 hg ν hν => by
    by_cases h : ν < ghBs n x
    · exact ⟨⟨0, hl.bot_lt⟩, by show gtc 0 < x; rw [gtc_zero]; exact hx.pos,
        by show ν ≤ ghBs n x + rdc 0 x; rw [rdc_zero, add_zero]; exact h.le⟩
    · push Not at h
      have e : ghBs n x + (ν - ghBs n x) = ν := Ordinal.add_sub_cancel_of_le h
      have hμ : ν - ghBs n x < rdc a x := by
        rw [← e] at hν; exact (add_lt_add_iff_left _).1 hν
      obtain ⟨b, hb, hgb, eb⟩ := rdc_surj hx hx1.le ha hg hμ
      exact ⟨⟨b, hb⟩, hgb, by show ν ≤ ghBs n x + rdc b x; rw [eb, e]⟩
  pi := fun σ ρ _ _ hB hg => by
    obtain ⟨h1, h2⟩ := ghBs_pi hB n
    obtain ⟨h3, h4⟩ := rdc_pi hB ha hg
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    exact ⟨h5, by show pi σ ρ (ghBs n ρ + rdc a ρ) = ghBs n σ + rdc a σ; rw [h6, h2, h4]⟩
  dec := fun x hx _ hg => by
    obtain ⟨e1, e2, -⟩ := (gh_lg_shift hl ha).choose_spec.2.2 n x hx hg
    refine ⟨e1, e2, ?_⟩
    show ghBs n x + rdc (gh_lg_shift hl ha).choose x < ghBs n x + rdc a x
    exact (add_lt_add_iff_left _).2 (rdc_mono hx ha (gh_lg_shift hl ha).choose_spec.1 hg
      ((gh_lg_shift hl ha).choose_spec.2.1.trans_lt hg))
  lp_le := fun _ _ _ _ => le_rfl
  pkg := fun ρ τ δ h hg => by
    obtain ⟨a', l, d, -, -, hgl, hd, -, hF⟩ := rdc_lim_facts hl ha
    have hρE := upsPt_inE h.ρU
    obtain ⟨-, -, e3, -, -, e6⟩ := hF ρ hρE hg
    have hcb : OT.CB (tlg l d) ρ := cb_tlg hρE.pos (hgl.trans_lt hg) (hd.trans_lt hg)
    have h1 : 1 ≤ OT.ev (tlg l d) ρ := by rw [← e3]; exact one_le_iff_pos.2 (Gc.gc_lg_pos e6)
    refine GhPkg.congr h (GhPkg.of_img (h.pkg_ot hcb h1)) (fun y hyE _ hgy => ?_) hg
    obtain ⟨-, -, f3, -, -, -⟩ := hF y hyE hgy
    rw [← f3, ((gh_lg_shift hl ha).choose_spec.2.2 n y hyE hgy).2.2]

/-- The limit step: the union. -/
noncomputable def ghStLim (n : ℕ) (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (IH : ∀ b < a, GhSt n b) :
    GhSt n a :=
  ⟨ghLimB (ghFL n a hl ha IH), rfl, fun _ _ _ _ => rfl⟩

/-- **The recursion over `a`** from a start of the shift `n`. -/
noncomputable def ghRec (n : ℕ) (s : GhStart n) (a : Ordinal.{0}) : a < gfE → GhSt n a :=
  Ordinal.limitRecOn (motive := fun a => a < gfE → GhSt n a) a (fun _ => ghSt0 s)
    (fun b ih h => ghStSucc n b (ih ((lt_add_one b).trans h)) h)
    (fun b hb ih h => ghStLim n b hb h (fun c hc => ih c hc (hc.trans h)))

/-- **The data of the union at the code `ε_{Ω₁+1}·(n+2)`**: all layers of the shift `n`. -/
noncomputable def ghFN (n : ℕ) (s : GhStart n) : GhUF 0 where
  I := {a : Ordinal.{0} // a < gfE}
  K := fun a => (ghRec n s a.1 a.2).1
  gi := fun a => gtc a.1
  o := fun a x => ghBs n x + rdc a.1 x
  l := ghBs (n + 1)
  lp := ghBs n
  i0 := ⟨0, eW_E.pos⟩
  ip := ⟨0, eW_E.pos⟩
  g_le := fun a => (ghRec n s a.1 a.2).2.1.le
  gi0 := gtc_zero
  gip := gtc_zero.le
  E_eq := fun a x hx hx1 hg => (ghRec n s a.1 a.2).2.2 x hx hx1 hg
  o_lt := fun a x hx _ _ hg => by rw [ghBs_succ]; exact (add_lt_add_iff_left _).2 (rdc_lt_eN hx a.1 hg)
  l_lt := fun x hx hx1 _ => ghBs_lt hx hx1 (n + 1)
  lim := fun x _ _ _ => by rw [ghBs_succ]; exact isSuccLimit_add _ (gh_eN_lim x)
  cof := fun x hx _ _ ν hν => by
    by_cases h : ν < ghBs n x
    · exact ⟨⟨0, eW_E.pos⟩, by show gtc 0 < x; rw [gtc_zero]; exact hx.pos,
        by show ν ≤ ghBs n x + rdc 0 x; rw [rdc_zero, add_zero]; exact h.le⟩
    · push Not at h
      have e : ghBs n x + (ν - ghBs n x) = ν := Ordinal.add_sub_cancel_of_le h
      have hμ : ν - ghBs n x < eN x := by
        rw [ghBs_succ, ← e] at hν; exact (add_lt_add_iff_left _).1 hν
      obtain ⟨k, hk⟩ := ghTw_cof hx hμ
      exact ⟨⟨ghTw k, ghTw_lt k⟩, (ghTw_gtc k).trans_lt (lu_one_lt_E hx),
        by show ν ≤ ghBs n x + rdc (ghTw k) x; rw [← e]; exact add_le_add le_rfl hk.le⟩
  pi := fun _ _ _ _ hB _ => ghBs_pi hB (n + 1)
  dec := fun x _ _ _ => by
    obtain ⟨e1, e2, e3⟩ := gh_lg_eNm x (n + 1)
    refine ⟨?_, ?_, ?_⟩
    · show ghBs (n + 1) x = ghBs n x + ω ^ lg (ghBs (n + 1) x)
      unfold ghBs; rw [e3]; exact e1
    · show ω ^ lg (ghBs (n + 1) x) ∣ ghBs n x
      unfold ghBs; rw [e3]; exact e2
    · show ghBs n x < ghBs (n + 1) x
      rw [ghBs_succ]; exact lt_add_of_pos_right _ (eN_E x).pos
  lp_le := fun _ _ _ _ => le_self_add
  pkg := fun ρ τ δ h hg => GhPkg.congr h (GhPkg.of_img h.pkg_eN)
    (fun y _ _ _ => by show eN y = lg (ghBs (n + 1) y); unfold ghBs; rw [(gh_lg_eNm y (n + 1)).2.2]) hg

/-- The next start: the union of the shift `n`. -/
noncomputable def ghStartNext (n : ℕ) (s : GhStart n) : GhStart (n + 1) :=
  ⟨ghLimB (ghFN n s), rfl, fun _ _ _ => rfl⟩

/-- The start of the shift `0`: the layer of the code `ε_{Ω₁+1}` (`R2.GhEps`). -/
noncomputable def ghStart0 : GhStart 0 :=
  ⟨ghEB, rfl, fun x _ _ => by rw [ghEB_E, ghBs_zero]⟩

/-- **The starts of all shifts.** -/
noncomputable def ghS : (n : ℕ) → GhStart n
  | 0 => ghStart0
  | n + 1 => ghStartNext n (ghS n)

/-- **THE GATED LAYER OF THE CODE `ε_{Ω₁+1}·(n+1) + a`** (`a < ε_{Ω₁+1}`). -/
noncomputable def ghB (n : ℕ) (a : Ordinal.{0}) (ha : a < gfE) : GdB := (ghRec n (ghS n) a ha).1

theorem ghB_g (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) : (ghB n a ha).g = gtc a := (ghRec n (ghS n) a ha).2.1

theorem ghB_E (n : ℕ) {a x : Ordinal.{0}} (ha : a < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc a < x) :
    (ghB n a ha).K.E x = gq (ghBs n x + rdc a x) x := (ghRec n (ghS n) a ha).2.2 x hx hx1 hg

theorem ghB_top (n : ℕ) {a x : Ordinal.{0}} (ha : a < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc a < x) :
    (ghB n a ha).K.sys.top x = gq (ghBs n x + rdc a x) x := by
  have hg' : (ghB n a ha).g < x := by rw [ghB_g]; exact hg
  rw [(ghB n a ha).K.top_eq x hx hx1 hg', ← ghB_E n ha hx hx1 hg]
  exact (ghB n a ha).ek x hx hx1 hg'

/-- **THE GENERIC THEOREM for the codes `ε_{Ω₁+1}·(n+1) + a`**: for every `n < ω` and every code `a < ε_{Ω₁+1}` there
is a gated base package (a gated layer with EXACT, IMG, RS and the top witness as fields) with gate `gtc a` whose top is
`ϑˣ(Ω₁·Ω₁ + ε_{x+1}·(n+1) + a(x)) = Γ_{x+1+ε_{x+1}·(n+1)+a(x)}` at every `ε`-number base `x < Ω₁` above `gtc a`. -/
theorem ghB_spec : ∀ (n : ℕ) (a : Ordinal.{0}), a < gfE → ∃ B : GdB, B.g = gtc a ∧
    ∀ x, InE x → x < Om1 → gtc a < x →
      B.K.E x = gq (eN x * ((n + 1 : ℕ) : Ordinal.{0}) + rdc a x) x ∧
        B.K.sys.top x = gq (eN x * ((n + 1 : ℕ) : Ordinal.{0}) + rdc a x) x :=
  fun n a ha => ⟨ghB n a ha, ghB_g n ha, fun x hx hx1 hg => ⟨ghB_E n ha hx hx1 hg, ghB_top n ha hx hx1 hg⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Gh
