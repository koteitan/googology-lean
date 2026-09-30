import Googology.Trans.BMS.PoR.PSS.Main.LocSpec
import Googology.Trans.BMS.PoR.PSS.Main.Nodes

/-!
# Fact BAR (`proof/PROOF-4.md` §15.1)

**Fact BAR** (`factBar`).  Let `α = ω^ζ ∈ (1, T¹ ∩ Ω_1)` with
`ζ =_CNF ω^{ζ_1} + ⋯ + ω^{ζ_k}`, `k ≥ 2`.  Then `ᾱ = ω^{ζ'}` with
`ζ' = ω^{ζ_1} + ⋯ + ω^{ζ_{k-1}}`.

The paper derives it from [CW12] Lemmas 5.4 and 5.10.  Here it is proved from
[CW12] Def 5.1 directly: the term of `α` is `ϑ_0(ζ)` (or `ϑ_0(ζ - 1)` when
`ζ = ε + n`, by (Exp)), and in the one case where Def 5.1 takes `α_{n-1}`
(`ζ = ε + η_0` with `ε` an epsilon number) the predecessor in the localization
is `ε`, the subterm above all others (`locPred_eq_of_top`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

/-! ## Terms of `T¹` below `Ω_1` -/

theorem valS_eq_sum_map : ∀ x : List WP, WP.valS x = (x.map WP.val).sum
  | [] => by simp
  | p :: x => by rw [WP.valS_cons, valS_eq_sum_map x]; simp

theorem pr_val {p : WP} (hp : NFP p) : Pr p.val :=
  ⟨val_isPrincipal hp, (val_pos hp).ne'⟩

theorem anf_of_nfs {x : List WP} (hx : NFS x) : ANF (x.map WP.val) :=
  ⟨fun v hv => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv; exact pr_val (hx.1 p hp),
    List.pairwise_map.mpr hx.2⟩

theorem lvl_eq_zero_of_val_lt {p : WP} (hp : NFP p) (h : p.val < Om 1) : p.lvl = 0 := by
  by_contra h0
  have := Om_le_val_of_le_lvl hp (Nat.one_le_iff_ne_zero.mpr h0)
  exact absurd h (not_lt.mpr this)

theorem exists_nfs_of_lt_T1bound {β : Ordinal.{0}} (h : β < T1bound) :
    ∃ u, NFS u ∧ WP.valS u = β ∧ ∀ q ∈ u, q.lvl = 0 := by
  have hne : T1set.Nonempty := ⟨0, [], NFS.nil, by simpa using Om_pos 1, by simp⟩
  obtain ⟨v, ⟨x, hx, hxv, rfl⟩, hβv⟩ := exists_lt_of_lt_csSup hne h
  obtain ⟨u, hu, rfl⟩ := seg hx hxv hβv
  refine ⟨u, hu, rfl, fun q hq => lvl_eq_zero_of_val_lt (hu.1 q hq) ?_⟩
  refine lt_of_le_of_lt ?_ (lt_trans hβv hxv)
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hq
  rw [valS_append, WP.valS_cons]
  exact le_trans le_self_add le_add_self

theorem eq_one_of_val {p : WP} (hp : NFP p) (h : p.val = 1) : p = TR.one :=
  eq_of_val_eq hp nfp_one (by rw [h, val_one])

theorem mem_starS {m : ℕ} {r : WP} : ∀ {x : List WP}, r ∈ starS m x → ∃ y ∈ x, r ∈ starP m y
  | [], h => by simp at h
  | y :: x, h => by
    rw [starS_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨y, by simp, h⟩
    · obtain ⟨z, hz, hr⟩ := mem_starS h
      exact ⟨z, by simp [hz], hr⟩

/-- A `ϑ_0`-subterm of a level-`0` term is at most it. -/
theorem val_le_of_mem_starP0 {p r : WP} (hp : NFP p) (hp0 : p.lvl = 0) (h : r ∈ starP 0 p) :
    r.val ≤ p.val := by
  obtain ⟨m, a⟩ := p
  simp only [WP.lvl_th] at hp0; subst hp0
  exact val_le_of_mem_sub0 hp h

/-- `α_{n-1} = q` when `q` is a subterm above all the others, with a larger argument
than `α`. -/
theorem locPred_eq_of_top {α q : WP} (hα : NFP α) (hα0 : α.lvl = 0) (hq : q ∈ sub0 α)
    (hq1 : 1 < q.val) (hqα : q.val < α.val) (harg : argV α < argV q)
    (htop : ∀ r ∈ sub0 α, r ≠ α → r.val ≤ q.val) : locPred α = q := by
  have hαmem : α ∈ sub0 α := by
    obtain ⟨m, a⟩ := α; simp only [WP.lvl_th] at hα0; subst hα0; exact self_mem_sub0
  have hsuf : SufMax α q := by
    refine ⟨hq, hq1, fun r hr hqr => ?_⟩
    by_cases hrα : r = α
    · rw [hrα]; exact harg
    · exact absurd (htop r hr hrα) (not_le.mpr hqr)
  refine locPred_eq hα hα0 hsuf hqα (fun q' hq' hq'α => ?_)
  have hne : q' ≠ α := fun e => by rw [e] at hq'α; exact lt_irrefl _ hq'α
  exact htop q' hq'.1 hne

/-- A level-`0` epsilon term has an argument of value at least `Ω_1`. -/
theorem Om_le_argV_of_eps {q : WP} (hq : NFP q) (he : isEpsLevel q 0 = true) :
    Om 1 ≤ argV q := by
  obtain ⟨h0, r, hr, hlr⟩ := isEpsLevel_iff.mp he
  obtain ⟨m, a⟩ := q
  cases a with
  | nil => simp at hr
  | cons r' a =>
    simp only [WP.arg_th, List.head?_cons, Option.mem_def, Option.some.injEq] at hr
    subst hr
    exact Om_le_valS_of_mem hq.nfs (by simp) hlr

theorem argV_th (m : ℕ) (a : List WP) : argV (.th m a) = WP.valS a := rfl

/-! ## The cases of bar -/

theorem barT_none {α : WP} (h : (argE α.arg).getLast? = none) : barT α = locPred α := by
  unfold barT; simp only [h]

theorem barT_pos {α η0 : WP} (h : (argE α.arg).getLast? = some η0)
    (hc : η0 = TR.one ∨ ((argE α.arg).dropLast ≠ [] ∧ ¬ supPt (argD α.arg) (argE α.arg).dropLast)) :
    barT α = .th 0 (argD α.arg ++ (argE α.arg).dropLast) := by
  unfold barT; simp only [h]; rw [if_pos hc]

theorem barT_neg {α η0 : WP} (h : (argE α.arg).getLast? = some η0)
    (hc : ¬ (η0 = TR.one ∨ ((argE α.arg).dropLast ≠ [] ∧
      ¬ supPt (argD α.arg) (argE α.arg).dropLast))) :
    barT α = locPred α := by
  unfold barT; simp only [h]; rw [if_neg hc]

/-! ## Fact BAR -/

theorem argD_of_lvl0 {x : List WP} (h : ∀ q ∈ x, q.lvl = 0) : argD x = [] := by
  cases x with
  | nil => rfl
  | cons q x => simp [argD, h q (by simp)]

theorem argE_of_lvl0 {x : List WP} (h : ∀ q ∈ x, q.lvl = 0) : argE x = x := by
  unfold argE
  rw [List.dropWhile_eq_self_iff]
  cases x with
  | nil => simp
  | cons q x => simp [h q (by simp)]

/-- `barO` at the value of a principal level-`0` term is the bar of that term. -/
theorem barO_eq {p : WP} (hp : NFP p) (hp0 : p.lvl = 0) : barO p.val = (barT p).val := by
  have hex : ∃ q : WP, NFP q ∧ q.lvl = 0 ∧ q.val = p.val := ⟨p, hp, hp0, rfl⟩
  unfold barO
  rw [dif_pos hex]
  have := eq_of_val_eq hex.choose_spec.1 hp hex.choose_spec.2.2
  rw [this]

/-- The subterms of `ϑ_0(x)` other than itself are at most the first summand of `x`. -/
theorem val_le_head_of_mem {x : List WP} (hx : NFS (q :: x)) (h0 : ∀ r ∈ q :: x, r.lvl = 0)
    {r : WP} (hr : r ∈ starS 0 (q :: x)) : r.val ≤ q.val := by
  obtain ⟨y, hy, hry⟩ := mem_starS hr
  have hyq : y.val ≤ q.val := by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_rfl
    · exact hx.le_head y hy
  exact le_trans (val_le_of_mem_starP0 (hx.1 y hy) (h0 y hy) hry) hyq

/-- **Fact BAR** (`proof/PROOF-4.md` §15.1). -/
theorem valS_dropLast_one {x : List WP} (hx : x ≠ []) (hl : x.getLast hx = TR.one) :
    WP.valS x = WP.valS x.dropLast + 1 := by
  conv_lhs => rw [← List.dropLast_append_getLast hx]
  rw [valS_append, hl, valS_single, val_one]

theorem eps_one_lt {q : WP} (hq : NFP q) (he : isEpsLevel q 0 = true) : 1 < q.val := by
  have := (eps_val hq ((isEpsLevel_iff.mp he).1 ▸ he)).1
  rwa [(isEpsLevel_iff.mp he).1, Om_zero] at this

theorem eps_fix {q : WP} (hq : NFP q) (he : isEpsLevel q 0 = true) : ω ^ q.val = q.val :=
  (eps_val hq ((isEpsLevel_iff.mp he).1 ▸ he)).2

theorem mem_sub0_of_head {q : WP} {x : List WP} (hq0 : q.lvl = 0) :
    q ∈ sub0 (.th 0 (q :: x)) := by
  rw [sub0_th, starS_cons]
  obtain ⟨m, a⟩ := q
  simp only [WP.lvl_th] at hq0; subst hq0
  simp [starP_th]

/-- **Fact BAR** (`proof/PROOF-4.md` §15.1). -/
theorem factBar {l : List Ordinal.{0}} (hl : ANF l) (hk : 2 ≤ l.length)
    (hT : ω ^ l.sum < T1bound) : barO (ω ^ l.sum) = ω ^ l.dropLast.sum := by
  have hζT : l.sum < T1bound := lt_of_le_of_lt (right_le_opow _ one_lt_omega0) hT
  obtain ⟨u, hu, hus, hu0⟩ := exists_nfs_of_lt_T1bound hζT
  have hul : u.map WP.val = l := anf_unique (anf_of_nfs hu) hl (by rw [← valS_eq_sum_map, hus])
  have hdrop : WP.valS u.dropLast = l.dropLast.sum := by
    rw [valS_eq_sum_map, ← hul, List.map_dropLast]
  have hlen : 2 ≤ u.length := by rw [← hul, List.length_map] at hk; exact hk
  obtain ⟨q, q2, u', rfl⟩ : ∃ q q2 u', u = q :: q2 :: u' := by
    rcases u with _ | ⟨q, _ | ⟨q2, u'⟩⟩
    · simp at hlen
    · simp at hlen
    · exact ⟨q, q2, u', rfl⟩
  have hq0 : q.lvl = 0 := hu0 q (by simp)
  have hqn : NFP q := hu.1 q (by simp)
  have hlvl : ∀ r ∈ q :: q2 :: u', r.lvl ≤ 0 := fun r hr => (hu0 r hr).le
  have hlt1 : WP.valS (q :: q2 :: u') < Om 1 := valS_lt_Om hu hlvl
  by_cases hA : isEpsPlusN (q :: q2 :: u') 0 = true
  · -- `ζ = ε + n`
    obtain ⟨hqe, hones⟩ := isEpsPlusN_cons.mp hA
    set d := (q :: q2 :: u').dropLast with hd
    have hdne : d ≠ [] := by simp [hd]
    have hdnfs : NFS d := hu.dropLast
    have hd0 : ∀ r ∈ d, r.lvl = 0 := fun r hr => hu0 r (List.mem_of_mem_dropLast hr)
    have hdA : isEpsPlusN d 0 = true := by
      rw [hd, List.dropLast_cons_of_ne_nil (by simp)]
      exact isEpsPlusN_cons.mpr ⟨hqe, fun r hr => hones r (List.mem_of_mem_dropLast hr)⟩
    have hlast : (q :: q2 :: u').getLast (by simp) = TR.one := by
      rw [List.getLast_cons (by simp)]
      exact hones _ (List.getLast_mem (l := q2 :: u') (by simp))
    have hpn : NFP (.th 0 d) := nfp_th hdnfs (fun r hr => by rw [hd0 r hr]; omega)
    have hpv : (WP.th 0 d).val = ω ^ l.sum := by
      rw [val_exp_eps hpn hdA, ← hus, valS_dropLast_one (by simp) hlast]
    rw [← hpv, barO_eq hpn rfl]
    have hE : argE (WP.th 0 d).arg = d := argE_of_lvl0 hd0
    have hD : argD (WP.th 0 d).arg = [] := argD_of_lvl0 hd0
    rcases u' with _ | ⟨q3, u''⟩
    · -- `ζ = ε + 1`: the bar is `ε`
      have hdq : d = [q] := by simp [hd]
      have hq1 : q ≠ TR.one := fun e => by
        have := eps_one_lt hqn hqe; rw [e, val_one] at this; exact lt_irrefl _ this
      have hpn' : NFP (.th 0 [q]) := hdq ▸ hpn
      rw [barT_neg (η0 := q) (by rw [hE, hdq]; rfl) (by
        rw [hE, hdq]; simp [hq1])]
      rw [hdq]
      have hqmem : q ∈ starS 0 [q] := by
        rw [starS_cons]; obtain ⟨m, a⟩ := q; simp only [WP.lvl_th] at hq0; subst hq0
        simp [starP_th]
      have hqv : q.val < Om 1 := by
        have : q.val ≤ WP.valS (q :: q2 :: []) := le_valS_head
        exact lt_of_le_of_lt this hlt1
      have harg : argV (.th 0 [q]) < argV q := by
        rw [argV_th, valS_single]
        exact lt_of_lt_of_le hqv (Om_le_argV_of_eps hqn hqe)
      rw [locPred_eq_of_top hpn' rfl (mem_sub0_of_head hq0) (eps_one_lt hqn hqe)
        (star_lt_val hpn' q hqmem) harg
        (fun r hr hrp => by
          rw [sub0_th] at hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact absurd rfl hrp
          · exact val_le_head_of_mem (NFS.single hqn) (by simp [hq0]) hr)]
      have : l.dropLast.sum = q.val := by rw [← hdrop, hdq, valS_single]
      rw [this, eps_fix hqn hqe]
    · -- `ζ = ε + n`, `n ≥ 2`: the last `1` is dropped
      have hdlast : d.getLast hdne = TR.one := by
        have hmem := List.getLast_mem hdne
        have e : d = q :: (q2 :: q3 :: u'').dropLast := by
          rw [hd, List.dropLast_cons_of_ne_nil (by simp)]
        have hne2 : (q2 :: q3 :: u'').dropLast ≠ [] := by simp
        have : d.getLast hdne = ((q2 :: q3 :: u'').dropLast).getLast hne2 := by
          simp only [e]; rw [List.getLast_cons hne2]
        rw [this]
        exact hones _ (List.mem_of_mem_dropLast (List.getLast_mem hne2))
      have hdd : d.dropLast ≠ [] := by simp [hd]
      rw [barT_pos (η0 := TR.one) (by rw [hE, List.getLast?_eq_some_getLast hdne, hdlast]) (by
        left; rfl)]
      rw [hD, hE, List.nil_append]
      have hdd0 : ∀ r ∈ d.dropLast, r.lvl = 0 := fun r hr => hd0 r (List.mem_of_mem_dropLast hr)
      have hddA : isEpsPlusN d.dropLast 0 = true := by
        rw [hd, List.dropLast_cons_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil (by simp)]
        exact isEpsPlusN_cons.mpr ⟨hqe, fun r hr => hones r
          (List.mem_of_mem_dropLast (List.mem_of_mem_dropLast hr))⟩
      have hpn2 : NFP (.th 0 d.dropLast) := nfp_th hdnfs.dropLast (fun r hr => by rw [hdd0 r hr]; omega)
      rw [val_exp_eps hpn2 hddA, ← hdrop, valS_dropLast_one hdne hdlast]
  · -- `ζ` is not `ε + n`: the term is `ϑ_0(ζ)`
    have hB : isEpsPlusN (q :: q2 :: u') 0 = false := by simpa using hA
    set u := q :: q2 :: u' with hudef
    have hpn : NFP (.th 0 u) := nfp_th hu (fun r hr => by rw [hu0 r hr]; omega)
    have hpv : (WP.th 0 u).val = ω ^ l.sum := by
      rw [val_exp hpn hlvl hB, ← hus]; simp [expBase]
    rw [← hpv, barO_eq hpn rfl]
    have hE : argE (WP.th 0 u).arg = u := argE_of_lvl0 hu0
    have hD : argD (WP.th 0 u).arg = [] := argD_of_lvl0 hu0
    have hune : u ≠ [] := by simp [hudef]
    set η0 := u.getLast hune with hη0
    have hget : (argE (WP.th 0 u).arg).getLast? = some η0 := by
      rw [hE, List.getLast?_eq_some_getLast hune]
    have hdne : u.dropLast ≠ [] := by simp [hudef]
    have hd0 : ∀ r ∈ u.dropLast, r.lvl = 0 := fun r hr => hu0 r (List.mem_of_mem_dropLast hr)
    by_cases hc : η0 = TR.one ∨ (u.dropLast ≠ [] ∧ ¬ supPt [] u.dropLast)
    · rw [barT_pos hget (by rw [hE, hD]; exact hc), hD, hE, List.nil_append]
      have hpn2 : NFP (.th 0 u.dropLast) := nfp_th hu.dropLast (fun r hr => by rw [hd0 r hr]; omega)
      -- the prefix is not `ε + n`
      have hB2 : isEpsPlusN u.dropLast 0 = false := by
        by_contra hA2
        have hA2' : isEpsPlusN u.dropLast 0 = true := by simpa using hA2
        obtain ⟨e, r, her⟩ := List.exists_cons_of_ne_nil hdne
        rw [her] at hA2'
        obtain ⟨hee, hr1⟩ := isEpsPlusN_cons.mp hA2'
        have hu_eq : u = e :: r ++ [η0] := by rw [← her, hη0, List.dropLast_append_getLast]
        have hη0n : NFP η0 := hu.1 η0 (List.getLast_mem hune)
        rcases r.eq_nil_or_concat with hr | ⟨r', z, hrz⟩
        · -- `u = [ε, η0]`
          subst hr
          rcases hc with hc | ⟨-, hc⟩
          · apply hA
            rw [hu_eq]
            exact isEpsPlusN_cons.mpr ⟨hee, by simp [hc]⟩
          · apply hc
            rw [her]
            have hen : NFP e := hu.1 e (by rw [hu_eq]; simp)
            refine ⟨e, rfl, (isEpsLevel_iff.mp hee).1, ?_, by simp⟩
            obtain ⟨-, r0, hr0, hlr0⟩ := isEpsLevel_iff.mp hee
            obtain ⟨m, a⟩ := e
            cases a with
            | nil => simp at hr0
            | cons r0' a =>
              simp only [WP.arg_th, List.head?_cons, Option.mem_def, Option.some.injEq] at hr0
              subst hr0
              simp only [argD, WP.valS_nil, WP.arg_th]
              rw [List.takeWhile_cons_of_pos (by simpa using hlr0), WP.valS_cons]
              exact lt_of_lt_of_le (val_pos (hen.of_mem (by simp))) le_self_add
        · -- `u = ε + ones + η0` with a `1` before `η0`, so `η0 = 1`
          have hz : z = TR.one := hr1 z (by rw [hrz]; simp)
          have hle : η0.val ≤ z.val := by
            have hp := hu.2
            rw [hu_eq, hrz] at hp
            simp only [List.cons_append, List.pairwise_cons, List.pairwise_append] at hp
            exact hp.2.2.2 z (by simp) η0 (by simp)
          rw [hz, val_one] at hle
          have hη1 : η0 = TR.one := eq_one_of_val hη0n (le_antisymm hle (one_le_val hη0n))
          apply hA
          rw [hu_eq]
          refine isEpsPlusN_cons.mpr ⟨hee, fun x hx => ?_⟩
          rcases List.mem_append.mp hx with hx | hx
          · exact hr1 x hx
          · rw [List.mem_singleton.mp hx]; exact hη1
      rw [val_exp hpn2 (fun r hr => (hd0 r hr).le) hB2, ← hdrop]
      simp [expBase]
    · -- `η' = ε` is a sup-point and `η0 ≠ 1`: the bar is `ε`
      push Not at hc
      obtain ⟨hη1, hsup⟩ := hc
      obtain ⟨e, he, he0, hΔ, -⟩ := hsup hdne
      rw [barT_neg hget (by rw [hE, hD]; push Not; exact ⟨hη1, fun _ => hsup hdne⟩)]
      -- `u = [ε, η0]`
      have hu2 : u' = [] := by
        cases u' with
        | nil => rfl
        | cons x u'' =>
          exfalso
          have : (u.dropLast).length = 1 := by rw [he]; rfl
          simp [hudef, List.length_dropLast] at this
      subst hu2
      have heq : e = q := by
        have : u.dropLast = [q] := by simp [hudef]
        rw [this] at he; exact (List.singleton_inj.mp he).symm
      subst heq
      have hee : isEpsLevel e 0 = true := by
        refine isEpsLevel_iff.mpr ⟨he0, ?_⟩
        obtain ⟨m, a⟩ := e
        cases a with
        | nil => simp [argD] at hΔ
        | cons r0 a =>
          refine ⟨r0, rfl, ?_⟩
          by_contra hlt
          push Not at hlt
          have : argD (r0 :: a) = [] := by
            simp [argD, show r0.lvl = 0 by omega]
          rw [WP.arg_th, this] at hΔ
          simp at hΔ
      have hemem : e ∈ starS 0 [e, q2] := by
        rw [starS_cons]; obtain ⟨m, a⟩ := e; simp only [WP.lvl_th] at hq0; subst hq0
        simp [starP_th]
      have harg : argV (.th 0 [e, q2]) < argV e := by
        rw [argV_th]
        exact lt_of_lt_of_le hlt1 (Om_le_argV_of_eps hqn hee)
      rw [locPred_eq_of_top hpn rfl (mem_sub0_of_head hq0) (eps_one_lt hqn hee)
        (star_lt_val hpn e hemem) harg
        (fun r hr hrp => by
          rw [sub0_th] at hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact absurd rfl hrp
          · exact val_le_head_of_mem hu hu0 hr)]
      have : l.dropLast.sum = e.val := by rw [← hdrop]; simp [hudef]
      rw [this, eps_fix hqn hee]

end Googology.Trans.PSS.Main
