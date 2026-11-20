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

private theorem coordinateInjection_apply
    {d : ℕ} (i : Fin d) (a : ℝ) :
    ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)) a =
      WithLp.toLp 2 (Pi.single i a) := by
  change (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm (Pi.single i a) = WithLp.toLp 2 (Pi.single i a)
  exact congrFun (PiLp.coe_symm_continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)) (Pi.single i a)

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- Assemble finitely many scalar restricted-`L²` maps as one map into the
existing Hilbert-vector-valued restricted-`L²` carrier. -/
noncomputable def hilbertVectorLpAssemble {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) :
    X →L[ℝ] PDE.HilbertVectorLp Ω 2 :=
  ∑ i, ((((PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)).compLpL
        (2 : ℝ≥0∞) (PDE.volumeOn Ω)).comp (L i))

/-- The assembled map has the canonical Hilbert-vector representative formed
from the scalar coordinate representatives. -/
theorem hilbertVectorLpAssemble_apply_ae {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) :
    ⇑(hilbertVectorLpAssemble L x) =ᵐ[PDE.volumeOn Ω]
      fun y => WithLp.toLp 2 (fun i => L i x y) := by
  let J : Fin d → ℝ →L[ℝ] PDE.HilbertVec d := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  let T : Fin d → PDE.ScalarLp Ω 2 →L[ℝ] PDE.HilbertVectorLp Ω 2 := fun i =>
    (J i).compLpL (2 : ℝ≥0∞) (PDE.volumeOn Ω)
  have hterm (i : Fin d) :
      ⇑(T i (L i x))
        =ᵐ[PDE.volumeOn Ω] fun y => WithLp.toLp 2 (Pi.single i (L i x y)) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (J i) (L i x)] with y hy
    rw [hy, coordinateInjection_apply]
  have hwhole : ⇑(hilbertVectorLpAssemble L x) =ᵐ[PDE.volumeOn Ω]
      fun y => ∑ i, WithLp.toLp 2 (Pi.single i (L i x y)) := by
    rw [hilbertVectorLpAssemble, sum_apply]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => T i (L i x)),
      ae_all_iff.mpr hterm] with y hy ht
    exact hy.trans (by rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _ => ht i)
  filter_upwards [hwhole] with y hy
  rw [hy]
  rw [← PiLp.coe_symm_continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => ℝ)]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
  ext i
  simp

/-- Projecting an assembled Hilbert-vector field recovers the corresponding
scalar restricted-`L²` map. -/
theorem hilbertVectorLpCoord_hilbertVectorLpAssemble {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Fin d → X →L[ℝ] PDE.ScalarLp Ω 2) (x : X) (i : Fin d) :
    PDE.hilbertVectorLpCoord Ω 2 i (hilbertVectorLpAssemble L x) = L i x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
    (hilbertVectorLpAssemble L x), hilbertVectorLpAssemble_apply_ae L x]
      with y hcoord hassemble
  rw [hcoord, hassemble]

/-- Restricted vector classes are determined by their scalar coordinates. -/
theorem hilbertVectorLp_ext
    {U V : PDE.HilbertVectorLp Ω 2}
    (h : ∀ i, PDE.hilbertVectorLpCoord Ω 2 i U = PDE.hilbertVectorLpCoord Ω 2 i V) : U = V := by
  apply MeasureTheory.Lp.ext
  have hi : ∀ᵐ y ∂PDE.volumeOn Ω, ∀ i : Fin d, U y i = V y i := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i U,
      PDE.coeFn_hilbertVectorLpCoord Ω 2 i V] with y hu hv
    rw [← hu, ← hv, h i]
  filter_upwards [hi] with y hy
  exact (WithLp.ofLp_injective 2) (funext hy)

end

end PDE
