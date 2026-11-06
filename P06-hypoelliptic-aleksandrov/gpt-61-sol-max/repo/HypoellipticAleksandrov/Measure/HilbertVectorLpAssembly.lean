module

public import PDEFoundation.Sobolev.W1p.Graph

/-!
# Finite assembly of Hilbert-vector-valued `L²` fields

This module assembles finitely many scalar restricted-volume `L²` continuous
linear maps into the existing Hilbert-vector-valued restricted `L²` carrier.
-/

@[expose] public section

noncomputable section


open scoped ENNReal

namespace PDE

variable {d : ℕ}

variable (i : Fin d)

private theorem coordinateInjection_apply
      (a : ℝ) :
    ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)) a =
      WithLp.toLp 2 (Pi.single i a) := by
  rfl

private theorem norm_coordinateInjection_le_one
      :
    ‖(PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [coordinateInjection_apply]
  rw [PiLp.norm_toLp_single]
  exact (one_mul ‖a‖).ge

variable {Ω : PDE.VelocityRegion d} {X : Type*}

/-- Assemble finitely many scalar restricted-`L²` maps as one map into the
existing Hilbert-vector-valued restricted-`L²` carrier. -/
def hilbertVectorLpAssemble

    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) :
    X →L[ℝ] PDE.HilbertVectorLp Ω 2 :=
  ∑ i, ((((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)).compLpL
        (2 ) (PDE.volumeOn Ω)).comp (L i))

/-- The assembled map has the canonical Hilbert-vector representative formed
from the scalar coordinate representatives. -/
theorem hilbertVectorLpAssemble_apply_ae

    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) :
    ⇑(hilbertVectorLpAssemble L x) =ᵐ[PDE.volumeOn Ω]
      fun y => WithLp.toLp 2 (fun i => L i x y) := by
  let sharedTerm_6c3130bef1 := ((fun _ : Fin d => ℝ))
  let J : Fin d → ℝ →L[ℝ] PDE.HilbertVec d := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ
      sharedTerm_6c3130bef1).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ sharedTerm_6c3130bef1 i)
  let T : Fin d → PDE.ScalarLp Ω 2 →L[ℝ] PDE.HilbertVectorLp Ω 2 := fun i =>
    (J i).compLpL (2 ) (PDE.volumeOn Ω)
  have hterm (i : Fin d) :
      ⇑(T i (L i x))
        =ᵐ[PDE.volumeOn Ω] fun y => WithLp.toLp 2 (Pi.single i (L i x y)) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (J i) (L i x)] with y hy
    rw [hy, coordinateInjection_apply]
  have hsum (s : Finset (Fin d)) :
      ⇑(∑ i ∈ s, T i (L i x))
        =ᵐ[PDE.volumeOn Ω] fun y =>
          ∑ i ∈ s, WithLp.toLp 2 (Pi.single i (L i x y)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact MeasureTheory.Lp.coeFn_zero _ 2 _
    | insert a s ha ih =>
      filter_upwards [MeasureTheory.Lp.coeFn_add
        (T a (L a x)) (∑ i ∈ s, T i (L i x)), ih,
        hterm a] with y hadd hsum hterm
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsum, hterm]
  have hwhole : ⇑(hilbertVectorLpAssemble L x)
      =ᵐ[PDE.volumeOn Ω] fun y =>
        ∑ i, WithLp.toLp 2 (Pi.single i (L i x y)) := by
    simpa only [hilbertVectorLpAssemble, sum_apply, ContinuousLinearMap.comp_apply, T, J]
      using hsum Finset.univ
  filter_upwards [hwhole] with y hy
  rw [hy]
  rw [← PiLp.coe_symm_continuousLinearEquiv 2 ℝ
    sharedTerm_6c3130bef1]
  apply (PiLp.continuousLinearEquiv 2 ℝ sharedTerm_6c3130bef1).injective
  ext i
  simp

/-- Projecting an assembled Hilbert-vector field recovers the corresponding
scalar restricted-`L²` map. -/
theorem hilbertVectorLpCoord_hilbertVectorLpAssemble

    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) (i : Fin d) :
    PDE.hilbertVectorLpCoord Ω 2 i (hilbertVectorLpAssemble L x) = L i x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
    (hilbertVectorLpAssemble L x), hilbertVectorLpAssemble_apply_ae L x]
      with y hcoord hassemble
  rw [hcoord, hassemble]

/-- The assembled map satisfies the finite coordinatewise triangle bound at
each input. -/
theorem norm_hilbertVectorLpAssemble_apply_le

    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) :
    ‖hilbertVectorLpAssemble L x‖ ≤ ∑ i, ‖L i x‖ := by
  let J : Fin d → ℝ →L[ℝ] PDE.HilbertVec d := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  let T : Fin d → PDE.ScalarLp Ω 2 →L[ℝ] PDE.HilbertVectorLp Ω 2 := fun i =>
    (J i).compLpL (2 ) (PDE.volumeOn Ω)
  rw [hilbertVectorLpAssemble]
  simp only [sum_apply]
  calc
    _ ≤ ∑ i, ‖T i (L i x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖L i x‖ := (Finset.sum_le_sum fun i a =>
  Trans.trans
    (Trans.trans (ContinuousLinearMap.le_opNorm (ContinuousLinearMap.compLpL 2 (volumeOn Ω) (J i)) ((L i) x))
      (mul_le_mul_of_nonneg_right
        (LE.le.trans (ContinuousLinearMap.norm_compLpL_le (J i)) (norm_coordinateInjection_le_one i))
        (norm_nonneg ((L i) x))))
    (one_mul ‖(L i) x‖))

end PDE
