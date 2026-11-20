module

public import OAI.NumberTheory.PrimeGaps.ContourIntegrals
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

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

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def laplaceFrequency (ℓ : V →L[ℝ] ℝ) (m u : V) : ℂ :=
  (ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceFrequency_re (ℓ : V →L[ℝ] ℝ) (m u : V) :
    (laplaceFrequency ℓ m u).re = ℓ m := by simp [laplaceFrequency]

noncomputable def positiveOrthantMeasure (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => volume.restrict (Ioi 0))

instance {α : Type*} [Fintype α] : SigmaFinite (positiveOrthantMeasure α) := by
  unfold positiveOrthantMeasure
  infer_instance

end FourierLaplace

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def coordinateDirectionList (ι : Type*) [Fintype ι] :
    List (EuclideanSpace ℝ ι) := by
  classical
  exact Finset.univ.toList.map (fun i => EuclideanSpace.single i (1:ℝ))

noncomputable def fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) : EuclideanSpace ℝ ι := by
  classical
  exact ∑ i∈Finset.univ.filter (fun i => b i=r), EuclideanSpace.single i (1:ℝ)

@[simp] theorem laplaceFrequency_coordinate {ι : Type*} [Fintype ι]
    (i : ι) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (EuclideanSpace.single i (1:ℝ)) u =
      frequencyW (u i) := by
  classical
  simp [laplaceFrequency,frequencyW,fourierCoordinateSum_apply,EuclideanSpace.inner_single_right]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceFrequency_sum {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    laplaceFrequency ℓ (∑ i∈S, m i) u = ∑ i∈S, laplaceFrequency ℓ (m i) u := by
  simp [laplaceFrequency,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]

@[simp] theorem laplaceFrequency_fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (fiberRay b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i) := by
  classical
  simp [fiberRay,laplaceFrequency_sum]

@[simp] theorem coordinateDirectionList_multiplier {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) :
    ((coordinateDirectionList ι).map (fun m => laplaceFrequency (fourierCoordinateSum ι) m u)).prod =
      ∏ i, frequencyW (u i) := by
  classical
  simp [coordinateDirectionList,List.map_map,Function.comp_def]

end SmallFiberCoefficient

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def negativeCube {ι : Type*} [Fintype ι] (T : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, -T≤x i ∧ x i≤0}

noncomputable def cubeIndicator {ι : Type*} [Fintype ι] (T : ℝ) : EuclideanSpace ℝ ι → ℝ :=
  (negativeCube T).indicator (fun _ => 1)

end LargePrimeGaps

end OAI
