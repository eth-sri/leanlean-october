module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Spatial slices of smooth neighborhood data

This module transfers the supplied smooth-neighborhood regularity on a closed
parabolic cylinder to the fixed-time spatial coefficient slices used in local
residual identities.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped Matrix.Norms.Elementwise

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (r₀ r₁ r : ℝ)

/-- A matrix-coefficient entry is spatially `C¹` at each time in the closed
time interval when the matrix field is smooth near the closed cylinder. -/
theorem contDiffOn_one_coefficientEntry_spatialSlice_of_smoothOnNeighborhood
     (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hr : r ∈ Set.Icc r₀ r₁) (i j : Fin d) :
    ContDiffOn ℝ 1 (fun y => a r y i j) Ω := by
  obtain ⟨U, _, hQU, haU⟩ := ha
  have hai : ContDiffOn ℝ PDE.smoothOrder
      (fun z : TimeVelocity d => a z.1 z.2 i) U :=
    (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haU
      (fun _ _ => Set.mem_univ _)
  have haij  :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hai
      (fun _ _ => Set.mem_univ _)

  have hslice  :=
    haij.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y hy =>
      hQU ⟨hr, subset_closure hy⟩
  exact hslice.of_le (by simp)

/-- A vector-field entry is continuous on each spatial slice at a time in the
closed interval when the vector field is smooth near the closed cylinder. -/
theorem continuousOn_vectorEntry_spatialSlice_of_smoothOnNeighborhood
     (b : PDE.TimeVectorField d)
    (hb : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hr : r ∈ Set.Icc r₀ r₁) (j : Fin d) :
    ContinuousOn (fun y => b r y j) Ω := by
  obtain ⟨U, _, hQU, hbU⟩ := hb
  have hbj  :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hbU
      (fun _ _ => Set.mem_univ _)

  exact (hbj.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y hy =>
    hQU ⟨hr, subset_closure hy⟩).continuousOn

end HypoellipticAleksandrov.Parabolic.Dirichlet
