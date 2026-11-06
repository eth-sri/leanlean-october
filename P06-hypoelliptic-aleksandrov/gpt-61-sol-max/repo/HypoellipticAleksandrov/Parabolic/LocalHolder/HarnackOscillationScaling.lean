module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillation
public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationGeometry

/-! # Structural homogeneous contraction on physical Euclidean cylinders -/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped Matrix.Norms.Elementwise

/-- The Harnack contraction transports with unchanged structural constants. -/
theorem exists_homogeneous_range_contraction
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ (A : CoefficientField N), IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (T : ℝ) (v₀ : PDE.Vec N) (r : ℝ), 0 < r →
      ∀ (v : HypoellipticAleksandrov.Parabolic.ScalarField N),
        IsScalarC12On v
          (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
        (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
          scalarTimeDerivative v z =
            matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) →
        ∀ l b : ℝ,
          (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
            l ≤ v z ∧ v z ≤ b) →
        ∃ l' b' : ℝ, b' - l' = θ * (b - l) ∧
          ∀ z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
            (PDE.euclideanBall v₀ (r / 2)), l' ≤ v z ∧ v z ≤ b' := by
  obtain ⟨h, hh, hh1, hc⟩ :=
    exists_unit_homogeneous_range_contraction N hN lam Lam hlam hLam
  refine ⟨1 - h, sub_nonneg.mpr hh1, by linarith only [hh], ?_⟩
  intro A hA hs hlo hhi T v₀ r hr v hv he l b hb


  let a := parabolicAffine (T - r ^ 2) v₀ r
  have hm  := parabolicAffine_mapsTo_backward_ball T v₀ hr

  obtain ⟨hvhat, hj⟩ := KrylovEstimate.scalarC12On_affine_pullback (isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)) v hv
    (T - r ^ 2) v₀ hr


  have hAc : IsContinuousCoefficientOn (pullbackCoefficient A (T - r ^ 2) v₀ r) (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) :=
    IsContinuousCoefficientOn.pullback
      (hA.continuous.continuousOn : IsContinuousCoefficientOn A (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r))) hm



  obtain ⟨l', b', hw, hbounds⟩ := hc
    _ (v ∘ a) hAc (by
        intro z _
        exact hs _ _) (by
        intro z _
        exact hlo _ _) (by
        intro z _
        exact hhi _ _) (by
        rcases hvhat with ⟨hv₀, ht, hv₂, hdt, hdg, hdh⟩
        exact ⟨hv₀.mono hm, fun z hz => ht z (hm hz), fun z hz => hv₂ z (hm hz),
          hdt.mono hm, hdg.mono hm, hdh.mono hm⟩) (by
        intro z hz
        rw [(hj z (hm hz)).1, (hj z (hm hz)).2, coefficientAt_pullbackCoefficient,
          matrixContraction_smul_right, he _ (hm hz)])
    l b (fun z hz => hb _ (hm hz))
  refine ⟨l', b', hw, ?_⟩
  intro z hz


  simpa only [Function.comp_def, a, parabolicAffine_inverse_apply T v₀ hr z] using (hbounds _ (backward_half_ball_inverse_mem T v₀ hr hz))

end HypoellipticAleksandrov.Parabolic.LocalHolder
