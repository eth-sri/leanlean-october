module

public import QPBT.Games.Sandwich.Support

/-! State-dependent overlap and distance estimates for products of measurements. -/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT.Pasting

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

section
variable {X α β I : Type*} [Fintype α] [Fintype β] [Fintype I] [DecidableEq I]

section

variable (D : Distribution X)
include D

section

variable (U V : X → α → Op I)
    (ψ : EuclideanSpace ℂ I)
include U V ψ

/-- The real inner product of two operator families applied to the shared state. -/
noncomputable def overlap : ℝ :=
  avgOver D (fun x => ∑ a, stateQForm ψ ((U x a)ᴴ * V x a))

theorem overlap_symm : overlap D U V ψ = overlap D V U ψ := by
  refine avgOver_congr _ _ _ fun x => Finset.sum_congr rfl fun a _ => ?_
  simp only [stateQForm_mul_eq_inner, Matrix.conjTranspose_conjTranspose]
  rw [← inner_conj_symm (𝕜 := ℂ) (applyOperatorToState (U x a) ψ), Complex.conj_re]

end

section

variable (U V R : X → α → Op I)
    (ψ : EuclideanSpace ℂ I)

theorem overlap_sub_left :
    overlap D U R ψ - overlap D V R ψ = overlap D (fun x a => U x a - V x a) R ψ := by
  unfold overlap
  simp_rw [← avgOver_sub, ← Finset.sum_sub_distrib, Matrix.conjTranspose_sub,
    sub_mul]
  simp [stateQForm, applyOperatorToState]

theorem overlap_self (U : X → α → Op I) (ψ : EuclideanSpace ℂ I) :
    overlap D U U ψ = opFamilyDistSq D U (fun _ _ => 0) ψ := by
  simp only [overlap, opFamilyDistSq, sub_zero, norm_applyOperatorToState_sq]

theorem abs_overlap_le_sqrt (U V : X → α → Op I)
    (ψ : EuclideanSpace ℂ I) {d : ℝ}
    (hU : opFamilyDistSq D U (fun _ _ => 0) ψ ≤ d)
    (hV : opFamilyDistSq D V (fun _ _ => 0) ψ ≤ 1) :
    |overlap D U V ψ| ≤ Real.sqrt d := by
  refine (abs_avgOver_inner_le D U V ψ).trans ?_
  simpa only [Real.sqrt_one, mul_one] using
    mul_le_mul (Real.sqrt_le_sqrt hU) (Real.sqrt_le_sqrt hV)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg d)

theorem abs_overlap_sub_le_sqrt {d : ℝ} (hUV : opFamilyDistSq D U V ψ ≤ d)
    (hR : opFamilyDistSq D R (fun _ _ => 0) ψ ≤ 1) :
    |overlap D U R ψ - overlap D V R ψ| ≤ Real.sqrt d := by
  rw [overlap_sub_left]
  exact abs_overlap_le_sqrt D _ R ψ (by simpa only [opFamilyDistSq, sub_zero] using hUV) hR

end

/-- If both products track a common isometric family, their overlap is close to one. -/
theorem overlap_lower (U V J : X → α → Op I)
    (ψ : EuclideanSpace ℂ I) {d : ℝ} (hU : opFamilyDistSq D U J ψ ≤ d)
    (hV : opFamilyDistSq D V J ψ ≤ d) (hVm : opFamilyDistSq D V (fun _ _ => 0) ψ ≤ 1)
    (hJ : opFamilyDistSq D J (fun _ _ => 0) ψ = 1) :
    1 - 2 * Real.sqrt d ≤ overlap D U V ψ := by
  have h₁ := (abs_le.mp (abs_overlap_sub_le_sqrt D U J V ψ hU hVm)).1
  have h₂ := (abs_le.mp (abs_overlap_sub_le_sqrt D V J J ψ hV hJ.le)).1
  rw [overlap_symm D V J, overlap_self, hJ] at h₂
  linarith

/-- Polarization for averaged state-dependent distances. -/
theorem distance_eq_overlap (U V : X → α → Op I)
    (ψ : EuclideanSpace ℂ I) :
    opFamilyDistSq D U V ψ = opFamilyDistSq D U (fun _ _ => 0) ψ +
      opFamilyDistSq D V (fun _ _ => 0) ψ - 2 * overlap D U V ψ := by
  simp only [opFamilyDistSq, overlap, sub_zero]
  simp_rw [norm_applyOperatorToState_sub_sq, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, avgOver_sub, avgOver_add, avgOver_const_mul]

theorem projective_mass_eq_one (A : X → Measurement α I)
    (ψ : EuclideanSpace ℂ I) (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hA : ∀ x, QPBT.Measurement.IsProjective (A x)) :
    opFamilyDistSq D (fun x a => (A x).effect a) (fun _ _ => 0) ψ = 1 := by
  refine (avgOver_congr D _ (fun _ => 1) fun x => ?_).trans
    (avgOver_const_of_isProbability D hD 1)
  simp_all [sub_zero, sum_norm_applyOperatorToState_sq, measurement_effect_hermitian, fun a => (hA x a).isIdempotentElem.eq, (A x).sum_eq_one, stateQForm_one, hψ, one_pow]

end

end

section
variable {X α I J : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem placed_dist_le (D : Distribution X) (A : X → Measurement α I)
    (B : X → Measurement α J) (ψ : EuclideanSpace ℂ (I × J)) {δ : ℝ}
    (h : bipartiteDefect D A B ψ ≤ δ) :
    measurementDistSq D (fun x => Measurement.rightPlacement (B x))
      (fun x => Measurement.leftPlacement (A x)) ψ ≤ 2 * δ := by
  rw [measurementDistSq, opFamilyDistSq_symm]
  exact (opFamilyDistSq_le_two_mul_consistencyDefect D
    (fun x => Measurement.leftPlacement (A x)) (fun x => Measurement.rightPlacement (B x)) ψ).trans
    (mul_le_mul_of_nonneg_left h (by norm_num))

end

end MIPStarRE.QPBT.Pasting
