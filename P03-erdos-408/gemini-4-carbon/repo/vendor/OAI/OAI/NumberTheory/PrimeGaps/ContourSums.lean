module

public import OAI.NumberTheory.PrimeGaps.EulerChoices

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

noncomputable def fourierCoordinateSum (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, EuclideanSpace.proj i

@[simp] theorem fourierCoordinateSum_apply {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    fourierCoordinateSum ι v = ∑ i, v i := by simp [fourierCoordinateSum]

noncomputable def divisorLogVector {ι : Type*} (L : ℝ) (d : ι → ℕ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.log (d i)/L)

@[simp] theorem divisorLogVector_apply {ι : Type*} (L : ℝ) (d : ι → ℕ) (i : ι) :
    divisorLogVector L d i = Real.log (d i)/L := rfl

noncomputable def fourierContour {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) : ℂ :=
  (1+Complex.I*(u i : ℂ))/(L:ℂ)

@[simp] theorem fourierContour_re {ι : Type*} (L : ℝ) (u : EuclideanSpace ℝ ι) (i : ι) :
    (fourierContour L u i).re = L⁻¹ := by
  simp [fourierContour, Complex.div_ofReal_re]

@[simp] theorem primeReciprocalPrefix_eq (y : ℕ) :
    primeReciprocalPrefix y = ∑ p∈Nat.primesLE y, (1:ℝ)/p := by
  simp only [primeReciprocalPrefix,primePrefix,one_div]
  exact Finset.sum_subtype_of_mem (fun p : ℕ => (p:ℝ)⁻¹) (fun p hp => (Nat.mem_primesLE.mp hp).2)

end LargePrimeGaps

end OAI
