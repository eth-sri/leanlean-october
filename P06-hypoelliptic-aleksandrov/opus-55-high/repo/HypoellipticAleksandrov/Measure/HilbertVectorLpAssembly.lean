module

public import PDEFoundation.Sobolev.W1p.Graph

/-!
# Finite assembly of Hilbert-vector-valued `L²` fields

This module assembles finitely many scalar restricted-volume `L²` continuous
linear maps into the existing Hilbert-vector-valued restricted `L²` carrier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace PDE

variable {d : ℕ} (i : Fin d)

private theorem norm_coordinateInjection_le_one
     :
    ‖(PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simp

/-- Assemble finitely many scalar restricted-`L²` maps as one map into the
existing Hilbert-vector-valued restricted-`L²` carrier. -/
def hilbertVectorLpAssemble
    {d : ℕ} {Ω : Set (PDE.Vec d)} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) :
    X →L[ℝ] PDE.HilbertVectorLp Ω 2 :=
  ∑ i, ((((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)).compLpL
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)).comp (L i))

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The assembled map has the canonical Hilbert-vector representative formed
from the scalar coordinate representatives. -/
theorem hilbertVectorLpAssemble_apply_ae
     {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) :
    ⇑(hilbertVectorLpAssemble L x) =ᵐ[PDE.volumeOn Ω]
      fun y => WithLp.toLp 2 (fun i => L i x y) := by
  let J : Fin d → ℝ →L[ℝ] PDE.HilbertVec d := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ
      _).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  let T : Fin d → PDE.ScalarLp Ω 2 →L[ℝ] PDE.HilbertVectorLp Ω 2 := fun i =>
    (J i).compLpL _ _
  have hterm (i : Fin d) :
      ⇑(T i (L i x))
        =ᵐ[PDE.volumeOn Ω] fun y => WithLp.toLp 2 (Pi.single i (L i x y)) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (J i) (L i x)] with y hy
    aesop
  have hsum (s : Finset _) :
      ⇑(∑ i ∈ s, T i (L i x))
        =ᵐ[PDE.volumeOn Ω] fun y =>
          ∑ i ∈ s, WithLp.toLp 2 (Pi.single i (L i x y)) := by
    induction s using Finset.induction_on with
    | empty =>
      exact MeasureTheory.Lp.coeFn_zero _ 2 _
    | insert a s ha ih =>
      filter_upwards [MeasureTheory.Lp.coeFn_add
        (T a (L a x)) (∑ i ∈ s, T i (L i x)), ih,
        hterm a] with y hadd hsum hterm
      simp_all
  have hwhole : ⇑(hilbertVectorLpAssemble L x)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        ∑ i, WithLp.toLp 2 (Pi.single i (L i x y)) := by
    simpa only [hilbertVectorLpAssemble, sum_apply, ContinuousLinearMap.comp_apply, T, J]
      using hsum Finset.univ
  filter_upwards [hwhole] with y hy
  aesop

/-- Projecting an assembled Hilbert-vector field recovers the corresponding
scalar restricted-`L²` map. -/
theorem hilbertVectorLpCoord_hilbertVectorLpAssemble
     {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) (i : Fin d) :
    PDE.hilbertVectorLpCoord Ω 2 i (hilbertVectorLpAssemble L x) = L i x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
    (hilbertVectorLpAssemble L x), hilbertVectorLpAssemble_apply_ae L x]
      with y hcoord hassemble
  simp_all

/-- The assembled map satisfies the finite coordinatewise triangle bound at
each input. -/
theorem norm_hilbertVectorLpAssemble_apply_le
     {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) :
    ‖hilbertVectorLpAssemble L x‖ ≤ ∑ i, ‖L i x‖ := by
  let J : Fin d → ℝ →L[ℝ] PDE.HilbertVec d := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ
      _).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  let T : Fin d → PDE.ScalarLp Ω 2 →L[ℝ] PDE.HilbertVectorLp Ω 2 := fun i =>
    (J i).compLpL _ _
  rw [hilbertVectorLpAssemble]
  simp only [sum_apply]
  calc
    _ ≤ ∑ i, ‖T i _‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖L i x‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖(J i).compLpL _ _‖ * ‖L i x‖ :=
          ((J i).compLpL _ _).le_opNorm _
        _ ≤ 1 * ‖L i x‖ := by
          apply mul_le_mul_of_nonneg_right
          · exact (ContinuousLinearMap.norm_compLpL_le _).trans
              (norm_coordinateInjection_le_one i)
          positivity
        _ = ‖L i x‖ := one_mul _

end PDE
