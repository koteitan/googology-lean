import Googology.Trans.PSS.TR.Mono

/-!
# Cofinality: definitions and helpers

`proof/TR-2.md` §4b.  For a term `a` and a sequence of terms `an n` (the
blocks `a⟨n⟩` of `a` in `M[n]`):

* `Bm m P γ`: every visible `ϑ_m`-subterm of `γ` satisfies `P`.  With `P = ⊤`
  this is the bound `True`; with `P s := ∃ n, s < θ_n` it is `B_m`.
* `LC m P a an` (**`LC_B(a)`**): every sum `γ` of `T¹` below `𝒯(a)` with `B(γ)`
  is below `𝒯(a⟨n⟩)` for all large `n`.
* `LCX m P c cn`: the X-form, with `X = log_ω 𝒯`.

Helpers: visible subterms under `log_ω`, of subterms, and below the first
summand (`star_le_head`); the prefix split of a sum (`prefix_split`); the
absorption prefix (`absorb_prefix`); (Inc) on `T¹` (`inc_le`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Visible subterms -/

theorem mem_starS_iff {m : ℕ} {x : List WP} {z : WP} :
    z ∈ starS m x ↔ ∃ p ∈ x, z ∈ starS m [p] := by
  induction x with
  | nil => simp
  | cons p l ih =>
    rw [starS_cons, List.mem_append, ih]
    simp only [List.mem_cons, starS_cons, starS_nil, List.append_nil]
    constructor
    · rintro (h | ⟨q, hq, hz⟩)
      · exact ⟨p, Or.inl rfl, h⟩
      · exact ⟨q, Or.inr hq, hz⟩
    · rintro ⟨q, rfl | hq, hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨q, hq, hz⟩

theorem starS_eq_nil_of_lvl_lt {m : ℕ} {x : List WP} (h : ∀ q ∈ x, q.lvl < m) : starS m x = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro z hz
  obtain ⟨p, hp, hz⟩ := mem_starS_iff.mp hz
  rw [starS_single_of_lt (h p hp)] at hz
  simp at hz

/-- Visible `ϑ_m`-subterms of `log_ω p`: those of `p`, `1` and `Ω_m`. -/
theorem mem_starS_logOmega' {m : ℕ} {p z : WP} (hp : NFP p) (hz : z ∈ starS m (logOmega p)) :
    z ∈ starS m [p] ∨ z = one ∨ z = om m := by
  rcases lt_trichotomy m p.lvl with hlt | heq | hgt
  · rcases mem_starS_logOmega hlt hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨l, a⟩ := p
    simp only [WP.lvl_th] at heq
    subst heq
    have harg : ∀ {z}, z ∈ starS m a → z ∈ starS m [WP.th m a] := fun hz =>
      mem_starS_single_of_le (p := .th m a) (by simp) hz
    simp only [logOmega, WP.lvl_th, WP.arg_th] at hz
    split_ifs at hz with h1 h2 h3
    · exact Or.inl hz
    · rw [starS_append, List.mem_append] at hz
      rcases hz with hz | hz
      · exact Or.inl (harg hz)
      · rcases mem_starS_single hz with ⟨-, rfl⟩ | ⟨-, hz⟩
        · exact Or.inr (Or.inl rfl)
        · simp [one] at hz
    · exact Or.inl (harg hz)
    · have hz' := starS_sublist m (addS_sublist _ _) hz
      rw [starS_append, List.mem_append] at hz'
      rcases hz' with hz' | hz'
      · rcases mem_starS_single hz' with ⟨-, rfl⟩ | ⟨-, hz'⟩
        · exact Or.inr (Or.inr rfl)
        · simp at hz'
      · exact Or.inl (harg hz')
  · -- `p` below level `m`: its log has no visible `ϑ_m`-subterm
    exfalso
    have hl := (logOmega_spec hp).2.2
    rw [starS_eq_nil_of_lvl_lt (fun q hq => lt_of_le_of_lt (hl q hq) hgt)] at hz
    simp at hz

/-- A visible `ϑ_m`-subterm of a visible `ϑ_k`-subterm (`m ≤ k`) is visible. -/
theorem starS_of_starS {m k : ℕ} (hmk : m ≤ k) :
    ∀ (β : List WP) {s z : WP}, s ∈ starS k β → z ∈ starS m [s] → z ∈ starS m β := by
  intro β
  induction β with
  | nil => intro s z hs; simp at hs
  | cons p l ihl =>
    intro s z hs hz
    rw [starS_cons, List.mem_append] at hs
    rcases hs with hs | hs
    · -- inside `p`
      have key : ∀ (p : WP) {s z : WP}, s ∈ starP k p → z ∈ starS m [s] → z ∈ starS m [p] := by
        intro p
        induction p using WP.ind with
        | h j a ih =>
          intro s z hs hz
          rw [starP_th] at hs
          split_ifs at hs with h1 h2
          · simp at hs
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact hz
            · -- `s` in the argument of `ϑ_k`
              obtain ⟨q, hq, hsq⟩ := mem_starS_iff.mp hs
              have := ih q hq (by simpa using hsq) hz
              exact mem_starS_single_of_le (p := .th j a) (by simp; omega)
                (starS_sublist m (List.singleton_sublist.mpr hq) this)
          · obtain ⟨q, hq, hsq⟩ := mem_starS_iff.mp hs
            have := ih q hq (by simpa using hsq) hz
            exact mem_starS_single_of_le (p := .th j a) (by simp; omega)
              (starS_sublist m (List.singleton_sublist.mpr hq) this)
      have := key p hs hz
      rw [starS_cons, List.mem_append]
      exact Or.inl (by simpa using this)
    · rw [starS_cons, List.mem_append]
      exact Or.inr (ihl hs hz)

/-- In a sum of level `≤ k`, every visible `ϑ_k`-subterm is at most the first
summand. -/
theorem star_le_head {k : ℕ} {σ : List WP} (hσ : NFS σ) (hl : ∀ q ∈ σ, q.lvl ≤ k) {z : WP}
    (hz : z ∈ starS k σ) : ∃ p r, σ = p :: r ∧ z.val ≤ p.val := by
  obtain ⟨q, hq, hzq⟩ := mem_starS_iff.mp hz
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hq)
  refine ⟨p, r, rfl, le_trans (val_le_of_mem_starS_single (hσ.1 q hq) hzq) ?_⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact le_rfl
  · exact hσ.le_head q hq

/-! ## The admissibility predicate -/

/-- `B(γ)`: every visible `ϑ_m`-subterm of `γ` satisfies `P`. -/
def Bm (m : ℕ) (P : WP → Prop) (γ : List WP) : Prop := ∀ s ∈ starS m γ, P s

theorem Bm.sublist {m : ℕ} {P : WP → Prop} {x y : List WP} (h : Bm m P y) (hxy : x.Sublist y) :
    Bm m P x := fun s hs => h s (starS_sublist m hxy hs)

theorem Bm.append {m : ℕ} {P : WP → Prop} {x y : List WP} (hx : Bm m P x) (hy : Bm m P y) :
    Bm m P (x ++ y) := by
  intro s hs
  rw [starS_append, List.mem_append] at hs
  rcases hs with hs | hs
  · exact hx s hs
  · exact hy s hs

theorem Bm.single_of_mem {m : ℕ} {P : WP → Prop} {γ : List WP} {p : WP} (h : Bm m P γ)
    (hp : p ∈ γ) : Bm m P [p] := h.sublist (List.singleton_sublist.mpr hp)

theorem Bm.log {m : ℕ} {P : WP → Prop} (hP1 : P one) (hPo : P (om m)) {p : WP} (hp : NFP p)
    (h : Bm m P [p]) : Bm m P (logOmega p) := by
  intro s hs
  rcases mem_starS_logOmega' hp hs with hs | rfl | rfl
  · exact h s hs
  · exact hP1
  · exact hPo

theorem Bm.arg {m : ℕ} {P : WP → Prop} {p : WP} (hm : m ≤ p.lvl) (h : Bm m P [p]) :
    Bm m P p.arg := fun s hs => h s (mem_starS_single_of_le hm hs)

theorem Bm.exp {m l : ℕ} {P : WP → Prop} (hml : m < l) {ξ : List WP} (h : Bm m P ξ) :
    Bm m P [omegaExp ξ l] := by
  intro s hs
  rcases mem_starS_omegaExp hs with ⟨hl, -⟩ | hs
  · omega
  · exact h s hs

theorem Bm.star {m k : ℕ} {P : WP → Prop} (hmk : m ≤ k) {β : List WP} {s : WP}
    (hs : s ∈ starS k β) (h : Bm m P β) : Bm m P [s] :=
  fun z hz => h z (starS_of_starS hmk β hs hz)

theorem Bm.top (m : ℕ) (γ : List WP) : Bm m (fun _ => True) γ := fun _ _ => trivial

/-! ## Cofinality -/

/-- **`LC_B(a)`**: every sum of `T¹` below `𝒯(a)` with `B` is eventually below
`𝒯(a⟨n⟩)`. -/
def LC (m : ℕ) (P : WP → Prop) (a : Tm) (an : ℕ → Tm) : Prop :=
  ∀ γ : List WP, NFS γ → WP.valS γ < (trTm a).val → Bm m P γ →
    ∃ n0, ∀ n ≥ n0, WP.valS γ < (trTm (an n)).val

/-- The X-form of `LC_B(c)`, with `X = log_ω 𝒯`. -/
def LCX (m : ℕ) (P : WP → Prop) (c : Tm) (cn : ℕ → Tm) : Prop :=
  ∀ ξ : List WP, NFS ξ → WP.valS ξ < WP.valS (logOmega (trTm c)) → Bm m P ξ →
    ∃ n0, ∀ n ≥ n0, WP.valS ξ < WP.valS (logOmega (trTm (cn n)))

/-- Finitely many eventual bounds have a common start. -/
theorem eventually_forall {α : Type*} {Q : α → ℕ → Prop} :
    ∀ L : List α, (∀ s ∈ L, ∃ n0, ∀ n ≥ n0, Q s n) → ∃ n0, ∀ n ≥ n0, ∀ s ∈ L, Q s n
  | [], _ => ⟨0, fun _ _ s hs => absurd hs List.not_mem_nil⟩
  | s :: L, h => by
    obtain ⟨a, ha⟩ := h s (by simp)
    obtain ⟨b, hb⟩ := eventually_forall L (fun s' hs' => h s' (by simp [hs']))
    refine ⟨max a b, fun n hn s' hs' => ?_⟩
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact ha n (le_trans (le_max_left _ _) hn)
    · exact hb n (le_trans (le_max_right _ _) hn) s' hs'

/-- A sum is below a principal value `E` if its first summand is. -/
theorem valS_lt_of_head {γ : List WP} (hγ : NFS γ) {E : Ordinal.{0}} (hE : IsPrincipal (· + ·) E)
    (hE0 : 0 < E) (h : ∀ p ∈ γ.head?, p.val < E) : WP.valS γ < E := by
  cases γ with
  | nil => simpa using hE0
  | cons g γ' =>
    refine valS_lt_of_forall hE hE0 (fun q hq => ?_)
    have hg := h g (by simp)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hg
    · exact lt_of_le_of_lt (hγ.le_head q hq) hg

/-- A sum whose first summand is `ω^ξ` is below `ω^{ξ+1}`. -/
theorem valS_lt_opow_succ {g : WP} {γ' : List WP} (hγ : NFS (g :: γ')) {ξ : Ordinal.{0}}
    (hg : g.val = ω ^ ξ) : WP.valS (g :: γ') < ω ^ (ξ + 1) :=
  valS_lt_of_head hγ (isPrincipal_add_omega0_opow _) (Ordinal.opow_pos _ omega0_pos) (fun p hp => by
    rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hp
    rw [← hp, hg]
    exact (opow_lt_opow_iff_right one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl))

/-! ## Splitting sums -/

/-- **The prefix split**: if `K ≤ ξ < K + w` where the summands of `K` are at
least the principal `w`, then `ξ = K ++ ξ'` with `ξ' < w`. -/
theorem prefix_split {w : WP} (hw : NFP w) :
    ∀ {K ξ : List WP}, NFS K → NFS ξ → (∀ p ∈ K, w.val ≤ p.val) → WP.valS K ≤ WP.valS ξ →
      WP.valS ξ < WP.valS K + w.val → ∃ ξ', ξ = K ++ ξ' ∧ NFS ξ' ∧ WP.valS ξ' < w.val
  | [], ξ, _, hξ, _, _, h2 => ⟨ξ, rfl, hξ, by simpa using h2⟩
  | k0 :: K, [], hK, _, _, h1, _ => by
    exfalso
    simp only [WP.valS_nil] at h1
    exact absurd (valS_pos (l := K) hK.head) (not_lt.mpr h1)
  | k0 :: K, x0 :: ξ, hK, hξ, hKw, h1, h2 => by
    rcases lt_trichotomy x0.val k0.val with hlt | heq | hgt
    · exact absurd h1 (not_le.mpr (lt_of_lt_of_le (valS_lt_of_head_lt hξ hK.head hlt)
        le_valS_head))
    · have hx := eq_of_val_eq hξ.head hK.head heq
      subst hx
      rw [WP.valS_cons, WP.valS_cons] at h1 h2
      rw [add_assoc] at h2
      obtain ⟨ξ', rfl, h3, h4⟩ := prefix_split hw hK.of_cons hξ.of_cons
        (fun p hp => hKw p (by simp [hp])) ((add_le_add_iff_left _).mp h1)
        ((add_lt_add_iff_left _).mp h2)
      exact ⟨ξ', rfl, h3, h4⟩
    · exfalso
      have hp := val_isPrincipal hξ.head
      have hKs : WP.valS K + w.val < x0.val := hp
        (valS_lt_of_forall hp (val_pos hξ.head) (fun q hq =>
          lt_of_le_of_lt (hK.le_head q hq) hgt))
        (lt_of_le_of_lt (hKw k0 (by simp)) hgt)
      have : WP.valS (k0 :: K) + w.val < WP.valS (x0 :: ξ) := by
        rw [WP.valS_cons, add_assoc]
        exact lt_of_lt_of_le (hp hgt hKs) le_valS_head
      exact absurd h2 (not_lt.mpr this.le)

/-- **The absorption prefix**: `W + w = K + w` for the prefix `K` of `W` of the
summands `≥ w`. -/
theorem absorb_prefix {W : List WP} (hW : NFS W) {w : WP} (hw : NFP w) :
    ∃ K, K <+: W ∧ NFS K ∧ (∀ p ∈ K, w.val ≤ p.val) ∧
      WP.valS K + w.val = WP.valS W + w.val := by
  set P : WP → Bool := fun p => cmpP p w == .lt with hP
  have hPv : ∀ p ∈ W, (P p = true ↔ p.val < w.val) := fun p hp => by
    simp only [hP, beq_iff_eq]
    exact cmpP_lt_iff (hW.1 p hp) hw
  have hup : W.Pairwise (fun a b => P a = true → P b = true) := by
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab hPa => ?_) hW.2
    exact (hPv b hb).mpr (lt_of_le_of_lt hab ((hPv a ha).mp hPa))
  have hadd : addS W [w] = W.takeWhile (fun a => !P a) ++ [w] := by
    rw [addS, Phi.reverse_dropWhile_reverse P hup]
  refine ⟨W.takeWhile (fun a => !P a), List.takeWhile_prefix _, hW.takeWhile _,
    fun p hp => ?_, ?_⟩
  · have h1 := List.mem_takeWhile_imp hp
    have hnp : ¬ (P p = true) := by simpa using h1
    exact not_lt.mp (fun h => hnp ((hPv p ((List.takeWhile_sublist _).subset hp)).mpr h))
  · have := (addS_spec hW (NFS.single hw)).2
    rw [hadd, valS_append, valS_single] at this
    exact this

theorem valS_le_of_prefix {K W : List WP} (h : K <+: W) : WP.valS K ≤ WP.valS W := by
  obtain ⟨R, rfl⟩ := h
  rw [valS_append]; exact le_self_add

/-! ## (Inc) on `T¹` -/

/-- **(Inc)** on `T¹`, from (C): `σ < σ'` gives `ϑ_k(Δ + σ) < ϑ_k(Δ + σ')`. -/
theorem inc_lt {k : ℕ} {Δ σ σ' : List WP} (hn : NFP (.th k (Δ ++ σ)))
    (hn' : NFP (.th k (Δ ++ σ'))) (hσ : ∀ q ∈ σ, q.lvl ≤ k) (hσ' : ∀ q ∈ σ', q.lvl ≤ k)
    (h : WP.valS σ < WP.valS σ') :
    (WP.th k (Δ ++ σ)).val < (WP.th k (Δ ++ σ')).val := by
  rw [val_lt_val_iff hn hn']
  left
  refine ⟨by rw [valS_append, valS_append]; exact (add_lt_add_iff_left _).mpr h, fun z hz => ?_⟩
  rw [starS_append, List.mem_append] at hz
  rcases hz with hz | hz
  · exact star_lt_val hn' z (by rw [starS_append]; exact List.mem_append_left _ hz)
  · have hσn : NFS σ := (NFS.append_iff.mp hn.nfs).2.1
    have hσn' : NFS σ' := (NFS.append_iff.mp hn'.nfs).2.1
    obtain ⟨p, r, rfl, hzp⟩ := star_le_head hσn hσ hz
    -- the first summand of `σ'` is at least `p`, and it is visible
    obtain ⟨p', r', he⟩ : ∃ p' r', σ' = p' :: r' := by
      cases σ' with
      | nil => exact absurd h (not_lt.mpr (by simp))
      | cons p' r' => exact ⟨p', r', rfl⟩
    subst he
    have hpp' : p.val ≤ p'.val := by
      by_contra hc
      exact absurd h (not_lt.mpr (le_trans (valS_lt_of_head_lt hσn' hσn.head (not_le.mp hc)).le
        le_valS_head))
    have hp'l : p'.lvl = k := by
      refine le_antisymm (hσ' p' (by simp)) ?_
      have hz1 := (starS_spec k _ hσn z hz).2.1
      have hzn := (starS_spec k _ hσn z hz).1
      rw [← hz1]
      exact lvl_le_of_val_le hzn hσn'.head (le_trans hzp hpp')
    have hp'star : p' ∈ starS k (Δ ++ p' :: r') := by
      rw [starS_append]
      exact List.mem_append_right _ (mem_starS_of_mem (by simp) hp'l)
    exact lt_of_le_of_lt (le_trans hzp hpp') (star_lt_val hn' p' hp'star)

theorem inc_le {k : ℕ} {Δ σ σ' : List WP} (hn : NFP (.th k (Δ ++ σ)))
    (hn' : NFP (.th k (Δ ++ σ'))) (hσ : ∀ q ∈ σ, q.lvl ≤ k) (hσ' : ∀ q ∈ σ', q.lvl ≤ k)
    (h : WP.valS σ ≤ WP.valS σ') :
    (WP.th k (Δ ++ σ)).val ≤ (WP.th k (Δ ++ σ')).val := by
  rcases h.lt_or_eq with h | h
  · exact (inc_lt hn hn' hσ hσ' h).le
  · have := eq_of_valS_eq (NFS.append_iff.mp hn.nfs).2.1 (NFS.append_iff.mp hn'.nfs).2.1 h
    rw [this]

end Googology.Trans.PSS.TR
