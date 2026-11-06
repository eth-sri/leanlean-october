module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.CenteredCutoffPiBernsteinConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedSpacetimeCompactSupport
public import HypoellipticAleksandrov.Parabolic.Dirichlet.FiniteSeparatedBernsteinAssembly
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives

/-!
# Density of finite separated spacetime tests

Smooth compactly supported spacetime tests, together with their time derivatives, are
approximated in squared integral by finite sums of separated time--space tests.
-/

 public section

open Filter Function Set




namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Smooth spacetime tests are approximated, together with their time derivative, by finite
separated tests whose factors all have support in one compact product. -/
theorem exists_finiteSeparatedSpacetimeTest_tendsto_integral_sq
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : PDE.VelocityRegion d}
    (hO : IsOpen O)
    (φ : TestFunction
      (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ )) :
    ∃ (Kt : TopologicalSpace.Compacts ℝ)
      (Ky : TopologicalSpace.Compacts (PDE.Vec d))
      (q : ℕ → FiniteSeparatedSpacetimeTest τ₁ τ₂ O),
      (Kt : Set ℝ) ⊆ Set.Ioo τ₁ τ₂ ∧
      (Ky : PDE.VelocityRegion d) ⊆ O ∧
      (∀ n m,
        tsupport ((q n).timeFactor m : ℝ → ℝ) ×ˢ
            tsupport ((q n).spatialFactor m : PDE.ScalarField d) ⊆
          (Kt : Set ℝ) ×ˢ (Ky : PDE.VelocityRegion d)) ∧
      Tendsto
        (fun n => ∫ z,
          ((q n).toFun z - φ z) ^ 2
          ∂timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => ∫ z,
          ((q n).timeDeriv z - timeDerivative φ z) ^ 2
          ∂timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O))
        atTop (nhds 0) := by
  obtain ⟨χ, hχ, hχone, hχcompact, hχO⟩ := exists_spacetimeTest_spatialCutoff hO φ
  obtain ⟨R, hR, hcube⟩ :=
    HypoellipticAleksandrov.Parabolic.Dirichlet.IsCompact.exists_subset_pi_Icc_vec hχcompact
  let Kt := spacetimeTestTimeSupportCompact φ
  let Ksp : PDE.VelocityRegion d := spacetimeTestSpatialSupportCompact φ

  choose q hqval hqderiv hqsupport using fun n =>
    exists_finiteSeparatedSpacetimeTest_cutoffPiBernstein
      (n := n) hO φ χ hχ hχcompact hχO R hR
  have hplateau : Set.EqOn χ 1 Ksp := by
    intro y hy

    exact ((subset_of_mem_nhdsSet hχone) hy)
  have hφsupport : tsupport (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) ⊆
      (Kt : Set ℝ) ×ˢ Ksp := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩


  let μ := timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)
  have hval := tendsto_integral_sq_cutoffPiBernsteinApproximation
    (Kt := Kt) (Ksp := Ksp) χ hχ.continuous hχcompact hplateau R hR hcube
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) φ.contDiff.continuous hφsupport (μ := μ)
  have hderiv := tendsto_integral_sq_cutoffPiBernsteinApproximation
    (Kt := Kt) (Ksp := Ksp) χ hχ.continuous hχcompact hplateau R hR hcube
    (timeDerivative (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)) (by
        unfold timeDerivative
        simpa using (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const) (by
        apply Subset.trans _ hφsupport
        unfold timeDerivative
        change closure (support (fun z => fderiv ℝ φ z (1, 0))) ⊆ tsupport (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
        refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
        intro z hz
        rw [mem_support] at hz ⊢
        intro hzero
        apply hz
        simp [hzero]) (μ := μ)
  refine ⟨Kt, (⟨tsupport χ, hχcompact⟩), q, ?_, hχO, ?_, ?_, ?_⟩
  · intro τ hτ
    rcases hτ with ⟨z, hz, rfl⟩
    exact (φ.tsupport_subset hz).1
  · intro n m
    exact hqsupport n m
  · simpa only [μ, hqval] using hval
  · simpa only [μ, hqderiv] using hderiv

end HypoellipticAleksandrov.Parabolic.Dirichlet
