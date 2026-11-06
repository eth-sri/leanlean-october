module

public import PottsDiscontinuity.SixVertex.InfinityLiftedChoices

/-! # Integer endpoint lifts of admissible defect choices -/

@[expose] public noncomputable section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

section
variable (x : Finset (Fin N)) (d : Fin (defects x).card → Bool)
@[simp] theorem indexedDefectChoice_ordered (a : Fin (defects x).card) :
    indexedDefectChoice x d
      ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ = d a := by
  change d ((defects x).orderIsoOfFin rfl |>.symm ((defects x).orderIsoOfFin rfl a)) = d a
  simp

/-- Cyclic finite endpoint of the indexed left/right move. -/
def choiceEndpoint (a : Fin (defects x).card) : Fin N :=
  if d a then prv ((defects x).orderEmbOfFin rfl a) else nxt ((defects x).orderEmbOfFin rfl a)

/-- Integer endpoint before sorting or cyclic reduction. -/
def choiceEndpointLift (a : Fin (defects x).card) : ℤ :=
  (((defects x).orderEmbOfFin rfl a).val : ℤ) + if d a then -1 else 1

theorem leftStepLift_eq_endpointLift  :
    leftStepLift (orderedDefectLift x) d = fun a => choiceEndpointLift x d a + a.val := by
  grind [leftStepLift, orderedDefectLift, defectCoordinate, choiceEndpointLift]

theorem choiceEndpoint_eq_motion (a : Fin (defects x).card) :
    choiceEndpoint x d a = defectMotion (horizontalOfDefectChoice x (indexedDefectChoice x d))
      ((defects x).orderEmbOfFin rfl a) := by
  have hh := horizontalOfDefectChoice_prv x (indexedDefectChoice x d)
    ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩
  simp_all [indexedDefectChoice_ordered, choiceEndpoint, defectMotion]

/-- The local admissibility condition on two canonically indexed neighboring defects. -/
theorem admissible_indexed_succ (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card)
    (hab : nxt ((defects x).orderEmbOfFin rfl a) = (defects x).orderEmbOfFin rfl b) :
    d a = false → d b = false := by
  intro hh
  have hmem : nxt ((defects x).orderEmbOfFin rfl a) ∈ defects x := by
    simp_all
  have hh' : indexedDefectChoice x d
      ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ = false := by
    simp_all
  have hc := ha ⟨(defects x).orderEmbOfFin rfl a, (defects x).orderEmbOfFin_mem rfl a⟩ hmem hh'
  simp_all
end

section
variable {x : Finset (Fin N)} (hx : NoConsecutiveUp x) (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
include hx ha
/-- Actual finite endpoints are injective for every admissible choice. -/
theorem choiceEndpoint_injective  :
    Function.Injective (choiceEndpoint x d) := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  intro a b hab
  apply (defects x).orderEmbOfFin rfl |>.injective
  apply hf.defectMotion_injective (disjoint_upperOfDefectChoice hx (indexedDefectChoice x d)) ((defects x).orderEmbOfFin_mem rfl a)
    ((defects x).orderEmbOfFin_mem rfl b)
  simp_all [choiceEndpoint_eq_motion]

/-- Endpoint membership in the actual upper defect set. -/
theorem choiceEndpoint_mem (a : Fin (defects x).card) :
    choiceEndpoint x d a ∈ defects (upperOfHorizontal (horizontalOfDefectChoice x (indexedDefectChoice x d))) := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  rw [hf.defects_eq_image (disjoint_upperOfDefectChoice hx (indexedDefectChoice x d))]
  exact mem_image.mpr ⟨_, (defects x).orderEmbOfFin_mem rfl a, (choiceEndpoint_eq_motion x d a).symm⟩

theorem card_upper_defects_choice  :
    (defects (upperOfHorizontal (horizontalOfDefectChoice x (indexedDefectChoice x d)))).card =
      (defects x).card := by
  have hf := flux_horizontalOfDefectChoice hx (indexedDefectChoice x d) ha
  have hd := disjoint_upperOfDefectChoice hx (indexedDefectChoice x d)
  rw [hf.defects_eq_image hd]
  exact card_image_of_injOn (hf.defectMotion_injective hd)
end

theorem prv_val_zero (i : Fin N) (hi : i.val = 0) : (prv i).val + 1 = N := by
  cases N with
  | zero => omega
  | succ k =>
    simp_all

section
variable (x : Finset (Fin N)) (d : Fin (defects x).card → Bool) (a : Fin (defects x).card)
theorem choiceEndpointLift_bounds  : -1 ≤ choiceEndpointLift x d a ∧ choiceEndpointLift x d a ≤ N := by
  grind [choiceEndpointLift]

/-- Exact cyclic reduction of the integer endpoint, with both seam branches explicit. -/
theorem choiceEndpoint_val  :
    ((choiceEndpoint x d a).val : ℤ) =
      if choiceEndpointLift x d a < 0 then choiceEndpointLift x d a + N
      else if (N : ℤ) ≤ choiceEndpointLift x d a then choiceEndpointLift x d a - N
      else choiceEndpointLift x d a := by
  let i := (defects x).orderEmbOfFin rfl a
  cases hd : d a
  · by_cases hn : i.val + 1 < N
    · have hn' := nxt_val_of_lt i hn
      simp only [choiceEndpoint, choiceEndpointLift, hd, Bool.false_eq_true, ↓reduceIte]
      grind
    · have hn' := nxt_val_wrap i (by omega)
      simp only [choiceEndpoint, choiceEndpointLift, hd, Bool.false_eq_true, ↓reduceIte]
      grind
  · by_cases hz : i.val = 0
    · have hp := prv_val_zero i hz
      simp only [choiceEndpoint, choiceEndpointLift, hd, ↓reduceIte]
      grind
    · have hp := prv_val_of_pos i (by omega)
      simp only [choiceEndpoint, choiceEndpointLift, hd, ↓reduceIte]
      grind
end

section
variable {x : Finset (Fin N)} (hx : NoConsecutiveUp x) (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
include hx ha
theorem choiceEndpointLift_injective  :
    Function.Injective (choiceEndpointLift x d) := by
  intro a b hab
  have h1 := choiceEndpoint_val x d a
  have h2 := choiceEndpoint_val x d b
  grind [choiceEndpoint, choiceEndpoint_injective]

/-- Valid integer endpoint lifts preserve the strict linear order before reducing modulo N. -/
theorem choiceEndpointLift_strictMono  :
    StrictMono (choiceEndpointLift x d) := by
  intro a b hab
  have hsite := (defects x).orderEmbOfFin rfl |>.strictMono hab
  have hne :=
    (choiceEndpointLift_injective hx d ha).ne (ne_of_lt hab)
  have hnoswap : ¬ (((defects x).orderEmbOfFin rfl b).val =
      ((defects x).orderEmbOfFin rfl a).val + 1 ∧ d a = false ∧ d b = true) := by
    rintro ⟨hv, hda, hdb⟩
    have hnext : nxt ((defects x).orderEmbOfFin rfl a) = (defects x).orderEmbOfFin rfl b := by
      apply Fin.ext
      rw [nxt_val_of_lt _ (by omega)]
      omega
    have hh := admissible_indexed_succ x d ha a b hnext hda
    simp_all
  grind [choiceEndpointLift]
end

section
variable {x : Finset (Fin N)}
theorem choiceEndpointLift_no_extremes (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card) :
    ¬ (choiceEndpointLift x d a = -1 ∧ choiceEndpointLift x d b = N) := by
  rintro ⟨ha0, hbN⟩
  have hda : d a = true := by
    cases hh : d a
    · grind [choiceEndpointLift]
    rfl
  have hdb : d b = false := by
    cases hh : d b
    · rfl
    grind [choiceEndpointLift]
  have hval0 : ((defects x).orderEmbOfFin rfl a).val = 0 := by
    simp_all [choiceEndpointLift]
  have hvalN : ((defects x).orderEmbOfFin rfl b).val + 1 = N := by
    grind [choiceEndpointLift]
  have hnext : nxt ((defects x).orderEmbOfFin rfl b) = (defects x).orderEmbOfFin rfl a := by
    apply Fin.ext
    rw [nxt_val_wrap _ hvalN, hval0]
  have hh := admissible_indexed_succ x d ha b a hnext hdb
  simp_all

/-- All endpoints remain in a cyclic interval of length strictly less than N. -/
theorem choiceEndpointLift_span (hN : 0 < N) (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice x (indexedDefectChoice x d))
    (a b : Fin (defects x).card) : choiceEndpointLift x d b - choiceEndpointLift x d a < N := by
  have h1 := choiceEndpointLift_bounds x d a
  have h2 := choiceEndpointLift_bounds x d b
  have hnot := choiceEndpointLift_no_extremes d ha a b
  have hne : choiceEndpointLift x d b - choiceEndpointLift x d a ≠ N := by
    have hfa := choiceEndpoint_val x d a
    have hfb := choiceEndpoint_val x d b
    grind [choiceEndpoint, choiceEndpoint_injective]
  omega
end

end PottsDiscontinuity.SixVertex
