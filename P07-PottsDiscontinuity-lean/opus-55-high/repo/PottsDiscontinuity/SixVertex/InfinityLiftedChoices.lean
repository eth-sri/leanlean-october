module

public import PottsDiscontinuity.SixVertex.InfinityChoices
public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.SixVertex.InfinityGround
public import PottsDiscontinuity.SixVertex.InfinityPhase

/-! # Indexed choices and collision cancellation on shifted lifts -/

@[expose] public noncomputable section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

section
variable (x : Finset (Fin N))
/-- Canonical integer version of the ordered shifted defect coordinates. -/
def orderedDefectLift  : Fin (defects x).card → ℤ :=
  fun a => defectCoordinate x a

/-- Read indexed choices on the canonical ordered defect sites. -/
def indexedDefectChoice (d : Fin (defects x).card → Bool) : DefectChoice x :=
  fun i => d ((defects x).orderIsoOfFin rfl |>.symm i)
end

/-- Left/right lifts with the convention `true = left` used by the defect choices. -/
def leftStepLift {k : ℕ} (x : Fin k → ℤ) (d : Fin k → Bool) : Fin k → ℤ :=
  fun a => x a + if d a then -1 else 1

section
variable {k : ℕ} (L : ℝ) (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b)
include hab
theorem sineLiftWeight_zero_of_factor (hs : Real.sin (Real.pi * ((x b : ℝ) - x a) / L) = 0) : sineLiftWeight L x = 0 := by
  have hs' : Real.sin (Real.pi * ((x a : ℝ) - x b) / L) = 0 := by
    have ht : Real.pi * ((x a : ℝ) - x b) / L = -(Real.pi * ((x b : ℝ) - x a) / L) := by ring
    simp_all
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply prod_eq_zero (mem_univ a)
    exact prod_eq_zero (mem_Ioi.mpr hab) hs
  · apply prod_eq_zero (mem_univ b)
    exact prod_eq_zero (mem_Ioi.mpr hba) hs'

theorem sineLiftWeight_zero_of_equal (hx : x a = x b) : sineLiftWeight L x = 0 := by
  apply sineLiftWeight_zero_of_factor L x hab
  simp_all
end

theorem sineLiftWeight_zero_of_period_difference {k : ℕ} (P : ℤ) (hP : P ≠ 0)
    (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b) (hx : x b - x a = P) :
    sineLiftWeight (P : ℝ) x = 0 := by
  apply sineLiftWeight_zero_of_factor (P : ℝ) x hab
  have hcast : (x b : ℝ) - x a = (P : ℝ) := by aesop
  simp_all

section
variable {k : ℕ} (s : Finset (Fin N)) (hs : s.card = k)
include s
/-- Canonically ordered sites a unit apart have consecutive ranks. -/
theorem orderEmbOfFin_rank_succ (a b : Fin k) (hv : (s.orderEmbOfFin hs b).val = (s.orderEmbOfFin hs a).val + 1) :
    b.val = a.val + 1 := by
  have hab : a < b := (s.orderEmbOfFin hs).lt_iff_lt.mp (by omega)
  by_contra hne
  let c : Fin k := ⟨a.val + 1, by omega⟩
  have hac : a < c := by grind
  have hcb : c < b := by grind
  have h1 := (s.orderEmbOfFin hs).strictMono hac
  have h2 := (s.orderEmbOfFin hs).strictMono hcb
  omega

theorem orderEmbOfFin_rank_zero (a : Fin k) (hv : (s.orderEmbOfFin hs a).val = 0) : a.val = 0 := by
  by_contra hne
  let b : Fin k := ⟨0, by omega⟩
  have hb : b < a := by grind
  have hp := (s.orderEmbOfFin hs).strictMono hb
  omega

theorem orderEmbOfFin_rank_last (a : Fin k) (hv : (s.orderEmbOfFin hs a).val + 1 = N) : a.val + 1 = k := by
  by_contra hne
  let b : Fin k := ⟨a.val + 1, by omega⟩
  have hb : a < b := by grind
  have hp := (s.orderEmbOfFin hs).strictMono hb
  omega
end

theorem nxt_val_wrap (i : Fin N) (hi : i.val + 1 = N) : (nxt i).val = 0 := by
  cases N with
  | zero => omega
  | succ k =>
    have he : i = Fin.last k := by grind
    simp_all

/-- Every inadmissible choice has zero sine weight, including a collision across the seam. -/
theorem sineLiftWeight_inadmissible (hN : 2 ≤ N) (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool)
    (ha : ¬ AdmissibleDefectChoice x (indexedDefectChoice x d)) :
    sineLiftWeight ((N : ℝ) + (defects x).card) (leftStepLift (orderedDefectLift x) d) = 0 := by
  unfold AdmissibleDefectChoice at ha
  push Not at ha
  obtain ⟨i, hj, hi, hnext⟩ := ha
  let e := (defects x).orderIsoOfFin rfl
  let a := e.symm i
  let b := e.symm ⟨nxt i.1, hj⟩
  have hav : (defects x).orderEmbOfFin rfl a = i.1 :=
    congrArg Subtype.val (e.apply_symm_apply i)
  have hbv : (defects x).orderEmbOfFin rfl b = nxt i.1 :=
    congrArg Subtype.val (e.apply_symm_apply ⟨nxt i.1, hj⟩)
  have hda : d a = false := hi
  have hdb : d b = true := by
    aesop
  by_cases hwrap : i.1.val + 1 < N
  · have hnv := nxt_val_of_lt i.1 hwrap
    have hrank := orderEmbOfFin_rank_succ (defects x) rfl a b (by omega)
    have hab : a ≠ b := by omega
    apply sineLiftWeight_zero_of_equal _ _ hab
    grind [leftStepLift, orderedDefectLift, defectCoordinate]
  · have hzero := nxt_val_wrap i.1 (by omega)
    have harank := orderEmbOfFin_rank_last (defects x) rfl a (by omega)
    have hbrank := orderEmbOfFin_rank_zero (defects x) rfl b (by omega)
    have hab : b ≠ a := by
      grind
    have hdiff : leftStepLift (orderedDefectLift x) d a -
        leftStepLift (orderedDefectLift x) d b = (N + (defects x).card : ℤ) := by
      grind [leftStepLift, orderedDefectLift, defectCoordinate]
    have hh := sineLiftWeight_zero_of_period_difference
      (N + (defects x).card : ℤ) (by omega) (leftStepLift (orderedDefectLift x) d) hab hdiff
    simp_all

end PottsDiscontinuity.SixVertex
