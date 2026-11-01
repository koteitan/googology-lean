import Googology.Notation.SSOS.Flat

/-!
Canonical parsing by adding one bit at a time. `snocOne` either extends the
last run, merges across a single zero, or starts a new maximal block.
This module uses no assumptions about the search expansion or standardness.
-/

namespace Googology.Notation.SSOS

def Binary (s : List ℕ) : Prop := ∀ n ∈ s, n = 0 ∨ n = 1

def snocOne : List U → List U
  | [] => [.b []]
  | .b u :: P => .b (snocOne u) :: P
  | [.z] => [.b [], .z]
  | .z :: .z :: P => .b [] :: .z :: .z :: P
  | .z :: .b u :: P => .b (.z :: u) :: P
termination_by t => sizeOf t
decreasing_by simp_wf; omega

theorem raiseBits_append_one (s : List ℕ) :
    raiseBits (s ++ [1]) = raiseBits s ++ [1] := by
  simp [raiseBits, raiseBit]

theorem raiseBits_append_zero (s : List ℕ) :
    raiseBits (s ++ [0]) = raiseBits s ++ [0,1] := by
  simp [raiseBits, raiseBit]

theorem flat_snocOne (t : List U) : flat (snocOne t) = flat t ++ [1] := by
  match t with
  | [] => simp [snocOne, raiseBits]
  | .b u :: P =>
    simp [snocOne, flat_snocOne u, raiseBits_append_one, List.append_assoc]
  | [.z] => simp [snocOne, raiseBits]
  | .z :: .z :: P => simp [snocOne, raiseBits, List.append_assoc]
  | .z :: .b u :: P => simp [snocOne, raiseBits_append_zero, List.append_assoc]
termination_by sizeOf t
decreasing_by simp_wf; omega

theorem canonical_snocOne (t : List U) (hc : Canonical t) : Canonical (snocOne t) := by
  match t with
  | [] => simpa only [snocOne] using Canonical.block .nil .nil trivial
  | .b u :: P =>
    have hu : Canonical u := by cases hc; assumption
    have hP : Canonical P := by cases hc; assumption
    have hg : BlockGap P := by cases hc; assumption
    simpa only [snocOne] using Canonical.block (canonical_snocOne u hu) hP hg
  | [.z] => simpa only [snocOne] using Canonical.block .nil (.zero .nil) trivial
  | .z :: .z :: P => simpa only [snocOne] using Canonical.block .nil hc trivial
  | .z :: .b u :: P =>
    cases hc with
    | zero h =>
      cases h with
      | block hu hP hg => simpa only [snocOne] using Canonical.block (.zero hu) hP hg
termination_by sizeOf t
decreasing_by simp_wf; omega

def parseStep (t : List U) (n : ℕ) : List U := if n = 0 then .z :: t else snocOne t

def parse (s : List ℕ) : List U := s.foldl parseStep []

@[simp] theorem parse_nil : parse [] = [] := rfl

theorem parse_append_zero (s : List ℕ) : parse (s ++ [0]) = .z :: parse s := by
  simp [parse, parseStep, List.foldl_append]

theorem parse_append_one (s : List ℕ) : parse (s ++ [1]) = snocOne (parse s) := by
  simp [parse, parseStep, List.foldl_append]

theorem canonical_parse (s : List ℕ) : Canonical (parse s) := by
  have aux : ∀ (s : List ℕ) (t : List U), Canonical t →
      Canonical (s.foldl parseStep t) := by
    intro s
    induction s with
    | nil => intro t ht; exact ht
    | cons n s ih =>
      intro t ht
      apply ih
      unfold parseStep
      split
      · exact .zero ht
      · exact canonical_snocOne t ht
  exact aux s [] .nil

theorem flat_parse (s : List ℕ) (hb : Binary s) : flat (parse s) = s := by
  have aux : ∀ (s : List ℕ) (t : List U), Binary s →
      flat (s.foldl parseStep t) = flat t ++ s := by
    intro s
    induction s with
    | nil => intro t _; simp
    | cons n s ih =>
      intro t hs
      have hn := hs n (by simp)
      have ht : Binary s := fun a ha => hs a (by simp [ha])
      rw [List.foldl_cons, ih _ ht]
      rcases hn with rfl | rfl <;>
        simp [parseStep, flat_snocOne, List.append_assoc]
  simpa [parse] using aux s [] hb

def popOne : List U → List U
  | .b [] :: P => P
  | .b (.z :: u) :: P => .z :: .b u :: P
  | .b (.b w :: Q) :: P => .b (popOne (.b w :: Q)) :: P
  | _ => []
termination_by t => sizeOf t
decreasing_by simp_wf; omega

theorem popOne_spec (u P : List U) (hc : Canonical (.b u :: P)) :
    Canonical (popOne (.b u :: P)) ∧
      snocOne (popOne (.b u :: P)) = .b u :: P ∧
      flat (.b u :: P) = flat (popOne (.b u :: P)) ++ [1] := by
  have hu : Canonical u := by cases hc; assumption
  have hP : Canonical P := by cases hc; assumption
  have hg : BlockGap P := by cases hc; assumption
  cases u with
    | nil =>
      simp only [popOne]
      refine ⟨hP, ?_, ?_⟩
      · cases P with
        | nil => simp [snocOne]
        | cons v Q =>
          cases v with
          | b v => exact False.elim hg
          | z =>
            cases Q with
            | nil => simp [snocOne]
            | cons v Q =>
              cases v with
              | b v => exact False.elim hg
              | z => simp [snocOne]
      · simp [raiseBits]
    | cons x Q => cases x with
      | z =>
        have hu' : Canonical Q := by cases hu; assumption
        simp only [popOne]
        exact ⟨.zero (.block hu' hP hg), by simp [snocOne], by
          simp [raiseBits_append_zero, List.append_assoc]⟩
      | b w =>
      obtain ⟨hcan, hsnoc, hflat⟩ := popOne_spec w Q hu
      simp only [popOne]
      refine ⟨.block hcan hP hg, ?_, ?_⟩
      · simp [snocOne, hsnoc]
      · rw [flat_b, hflat, raiseBits_append_one, flat_b, List.append_assoc]
termination_by sizeOf u
decreasing_by simp_all; omega

theorem parse_flat (t : List U) (hc : Canonical t) : parse (flat t) = t := by
  match t with
  | [] => simp
  | .z :: P =>
    have hP : Canonical P := by cases hc; assumption
    rw [flat_z, parse_append_zero, parse_flat P hP]
  | .b u :: P =>
    obtain ⟨hcan, hsnoc, hflat⟩ := popOne_spec u P hc
    rw [hflat, parse_append_one, parse_flat _ hcan, hsnoc]
termination_by (flat t).length
decreasing_by
  all_goals simp_all only [flat_z, List.length_append, List.length_singleton]; omega

theorem flat_injective {t t' : List U} (hc : Canonical t) (hc' : Canonical t')
    (h : flat t = flat t') : t = t' := by
  simpa [parse_flat t hc, parse_flat t' hc'] using congrArg parse h

theorem encode_injective {t t' : List U} (hc : Canonical t) (hc' : Canonical t')
    (h : encode t = encode t') : t = t' := by
  apply flat_injective hc hc'
  exact List.append_cancel_left h

theorem binary_encode_exists (Y : List ℕ) (hb : Binary Y) :
    ∃ t, Canonical t ∧ encode t = [0,0] ++ Y :=
  ⟨parse Y, canonical_parse Y, by simp [encode, flat_parse Y hb]⟩

end Googology.Notation.SSOS
