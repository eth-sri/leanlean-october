module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyExistence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothInteriorBootstrap
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnvelope
public import PDEFoundation.Calculus.RegularityOrder


/-! # Signed source corrections from the proved energy solver

The internal variational existence and interior bootstrap supply classical interior
corrections for arbitrary smooth signed forcing, without a compact source restriction.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set Dirichlet
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- The proved energy solver supplies an interior classical representative for signed sources. -/
theorem exists_signed_source_classicalInterior {d : ℕ} (hd : 0 < d)
    {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : HypoellipticAleksandrov.Parabolic.ScalarField d) (hF : ContDiff ℝ PDE.smoothOrder F) :
    ∃ (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
      (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g),
      IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu ∧
      ∃ w : HypoellipticAleksandrov.Parabolic.ScalarField d,
        MemLp w 2 (timeVelocityVolumeOn (Ioo a T ×ˢ Ω)) ∧
        (∀ᵐ t ∂volume.restrict (Ioo a T),
          (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) ∧
        IsScalarC12On w (scalarParabolicOpenCylinder a T Ω) ∧
        ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
          scalarTimeDerivative w z +
            matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z := by
  let sharedTerm_e9fdfce787 := ((fun t y => F (t, y)))
  have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  have hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  obtain ⟨u, g, hdu, hu⟩ := exists_reverseTime_variational_energy_solution a T lam Lam
    haT hlam hLam hΩ hΩb A (fun _ _ => 0) (fun _ _ => 0) sharedTerm_e9fdfce787
    hAs hbs hcs hFs (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
    (fun _ _ => le_rfl) 0
  obtain ⟨w, hwl, hwslice, hwr, hwe, _⟩ := exists_smoothInteriorBootstrap hd a T haT hΩ hΩb
    lam Lam hlam hLam A (fun _ _ => 0) (fun _ _ => 0) sharedTerm_e9fdfce787
    hAs hbs hcs hFs (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
    (fun _ _ => le_rfl) 0 u g hdu hu
  refine ⟨u, g, hdu, hu, w, hwl, hwslice, hwr, ?_⟩
  intro z hz
  simpa only [matrixContraction, coefficientAt, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Prod.mk.eta] using hwe z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder
