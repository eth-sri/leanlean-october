module
public import Mathlib

public import PottsDiscontinuity.SixVertex.InfinityChoices
public import PottsDiscontinuity.SixVertex.InfinityDescent
public import PottsDiscontinuity.SixVertex.InfinityGround
public import PottsDiscontinuity.SixVertex.InfinityPhase

/-! # Indexed choices and collision cancellation on shifted lifts -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

/-- Canonical integer version of the ordered shifted defect coordinates. -/
noncomputable def orderedDefectLift (x : Finset (Fin N)) : Fin (defects x).card → ℤ :=
  fun a => defectCoordinate x a

/-- Read indexed choices on the canonical ordered defect sites. -/
noncomputable def indexedDefectChoice (x : Finset (Fin N))
    (d : Fin (defects x).card → Bool) : DefectChoice x :=
  fun i => d ((defects x).orderIsoOfFin rfl |>.symm i)

/-- Left/right lifts with the convention `true = left` used by the defect choices. -/
def leftStepLift {k : ℕ} (x : Fin k → ℤ) (d : Fin k → Bool) : Fin k → ℤ :=
  fun a => x a + if d a then -1 else 1

section

variable {k : ℕ} (L : ℝ) (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b)
include hab

private theorem sineLiftWeight_zero_of_factor 
    (hs : Real.sin (Real.pi * ((x b : ℝ) - x a) / L) = 0) : sineLiftWeight L x = 0 := by
  
  rcases lt_or_gt_of_ne hab with hab | hba
  · apply prod_eq_zero (mem_univ a)
    exact prod_eq_zero (mem_Ioi.mpr hab) hs
  · apply prod_eq_zero (mem_univ b)
    exact prod_eq_zero (mem_Ioi.mpr hba) (by
                                            have ht : Real.pi * ( x a  - x b) / L = -(Real.pi * ( x b  - x a) / L) := by ring
                                            simp_all)

theorem sineLiftWeight_zero_of_equal  (hx : x a = x b) : sineLiftWeight L x = 0 := by
  apply sineLiftWeight_zero_of_factor L x hab
  rw [hx]
  simp

end

section

variable {k : ℕ}
include k

theorem sineLiftWeight_zero_of_period_difference  (P : ℤ) (hP : P ≠ 0)
    (x : Fin k → ℤ) {a b : Fin k} (hab : a ≠ b) (hx : x b - x a = P) :
    sineLiftWeight (P : ℝ) x = 0 := by
  apply sineLiftWeight_zero_of_factor  P  x hab
  have hcast :  x b  - x a = (P : ℝ) := by exact_mod_cast hx
  simp_all

section

variable (s : Finset (Fin N)) (hs : s.card = k)


/-- Canonically ordered sites a unit apart have consecutive ranks. -/
theorem orderEmbOfFin_rank_succ  
    (a b : Fin k) (hv : (s.orderEmbOfFin hs b).val = (s.orderEmbOfFin hs a).val + 1) :
    b.val = a.val + 1 := by
  have hab : a < b := (s.orderEmbOfFin hs).lt_iff_lt.mp (by  omega)
  by_contra hne
  let c : Fin k := ⟨a.val + 1, by omega⟩
  have hac : a < c := by change a.val < a.val + 1; omega
  have hcb : c < b := by change a.val + 1 < b.val; omega
  have h1 := (s.orderEmbOfFin hs).strictMono hac
  have h2 := (s.orderEmbOfFin hs).strictMono hcb
  omega

theorem orderEmbOfFin_rank_zero  
    (a : Fin k) (hv : (s.orderEmbOfFin hs a).val = 0) : a.val = 0 := by
  by_contra hne
  
  have hb :  ⟨0, by omega⟩  < a := by change 0 < a.val; omega
  have hp := (s.orderEmbOfFin hs).strictMono hb
  grind

theorem orderEmbOfFin_rank_last  
    (a : Fin k) (hv : (s.orderEmbOfFin hs a).val + 1 = N) : a.val + 1 = k := by
  by_contra hne
  
  have hb : a <  ⟨a.val + 1, by omega⟩  := by change a.val < a.val + 1; omega
  have hp := (s.orderEmbOfFin hs).strictMono hb
  grind

end

end

theorem nxt_val_wrap (i : Fin N) (hi : i.val + 1 = N) : (nxt i).val = 0 := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ k =>
    have he : i = Fin.last k := by
                                  bound
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
  have hav : (defects x).orderEmbOfFin rfl a = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
  have hbv : (defects x).orderEmbOfFin rfl b = nxt i.1 := congrArg Subtype.val (e.apply_symm_apply ⟨nxt i.1, hj⟩)
  have hda : d a = false := hi
  have hdb : d b = true := by
    aesop
  by_cases hwrap : i.1.val + 1 < N
  · have hnv := nxt_val_of_lt i.1 hwrap
    
    have hrank := orderEmbOfFin_rank_succ (defects x) rfl a b (by rw [hav, hbv, hnv])
    have hab : a ≠ b := by   omega
    apply sineLiftWeight_zero_of_equal _ _ hab
    simp only [leftStepLift, hda, hdb, Bool.false_eq_true, ↓reduceIte, orderedDefectLift, defectCoordinate]
    omega
  · 
    have hzero := nxt_val_wrap i.1 (by omega)
    have harank := orderEmbOfFin_rank_last (defects x) rfl a (by grind)
    have hbrank := orderEmbOfFin_rank_zero (defects x) rfl b (by rw [hbv]; exact hzero)
    have hab : b ≠ a := by
      grind
    
    
    have hh := sineLiftWeight_zero_of_period_difference
      (N + (defects x).card ) (by omega) (leftStepLift (orderedDefectLift x) d) hab (by
                                                                               grind [leftStepLift, orderedDefectLift, defectCoordinate])
    simpa only [Int.cast_add, Int.cast_natCast] using hh

end PottsDiscontinuity.SixVertex
