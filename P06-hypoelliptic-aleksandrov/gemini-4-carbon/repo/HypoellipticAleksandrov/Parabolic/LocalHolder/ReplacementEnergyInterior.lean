module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ParabolicHormanderRegularity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnvelope

/-! # Signed source corrections from the proved energy solver -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology MatrixOrder Matrix.Norms.Elementwise

/-- The proved energy solver supplies an interior classical representative for signed sources. -/
theorem exists_signed_source_classicalInterior {d : ℕ} (_hd : 0 < d)
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
      (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g),
      IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu ∧
      ∃ w : TimeVelocity d → ℝ,
        MemLp w 2 (timeVelocityVolumeOn (Ioo a T ×ˢ Ω)) ∧
        (∀ᵐ t ∂volume.restrict (Ioo a T),
          (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) ∧
        IsScalarC12On w (scalarParabolicOpenCylinder a T Ω) ∧
        ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
          scalarTimeDerivative w z +
            matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z := by
  obtain ⟨u, g, hdu, hu, w, hwl, hwslice, hwr, hwe⟩ :=
    exists_classicalInterior_of_variational_hormander hΩ hΩb a T haT lam Lam hlam hLam
      A (fun _ _ => 0) hA contDiff_const hlo hhi F hF
  refine ⟨u, g, hdu, hu, w, hwl, hwslice, hwr, fun z hz => ?_⟩
  simpa [PDE.vecDot] using hwe z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder
