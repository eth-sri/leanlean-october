module

public import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.Parabolic.Operator
public import HypoellipticAleksandrov.Parabolic.WeakJetExtension
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierLocalization
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Residual-bearing mollification of local weak parabolic equations

This file globalizes a cutoff selected weak jet and mollifies it on a compact
strict collar.  The resulting smooth functions satisfy the pointwise forward
equation with their explicit coefficient--Hessian commutator residual.  No
claim of residual decay or of a homogeneous classical equation is made here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/- The value obtained by right-convolving a global selected weak jet. -/
noncomputable def parabolicMollifiedValue
    {d p}
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → Real :=
  parabolicConvolution g.toFun (parabolicMollifier d n)

/- The matrix made by right-convolving the selected velocity Hessian entries. -/
noncomputable def parabolicMollifiedHessian
    {d p}
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → PDE.Mat d :=
  fun z i j => parabolicConvolution
    (fun y => g.velocityHessian y i j) (parabolicMollifier d n) z

/- The explicit coefficient--Hessian residual of this mollification. -/
noncomputable def weakEquationMollificationResidual
    {d p} (Aext : CoefficientField d)
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    TimeVelocity d → Real :=
  fun z =>
    parabolicConvolution
      (fun y => matrixContraction (coefficientAt Aext y) (g.velocityHessian y))
      (parabolicMollifier d n) z -
    matrixContraction
      (coefficientAt (parabolicMollifyCoefficient Aext n) z)
      (parabolicMollifiedHessian g n z)

/- Unfolding lemma for the selected-jet value mollification. -/
private theorem parabolicConvolution_eq_of_ae_eq_on_support
    {d f g rho O}
    (hO : MeasurableSet O) (z : TimeVelocity d)
    (hsupport : {y | rho (z - y) ≠ 0} ⊆ O)
    (heq : f =ᵐ[timeVelocityVolumeOn O] g) :
    parabolicConvolution f rho z = parabolicConvolution g rho z := by
  change (∫ y, f y * rho (z - y)) = ∫ y, g y * rho (z - y)
  apply integral_congr_ae
  have heq' : ∀ᵐ y ∂volume, y ∈ O → f y = g y := by
    change ∀ᵐ y ∂volume.restrict O, f y = g y at heq
    exact (ae_restrict_iff' hO).mp heq
  filter_upwards [heq'] with y hy
  by_cases hyO : y ∈ O
  · rw [hy hyO]
  · have hzero : rho (z - y) = 0 := by
      by_contra hne
      exact hyO (hsupport hne)
    simp [hzero]

private theorem parabolicConvolution_nonneg_of_ae_nonneg_on_support
    {d f rho O}
    (hO : MeasurableSet O) (z : TimeVelocity d)
    (hsupport : {y | rho (z - y) ≠ 0} ⊆ O)
    (hnonneg : ∀ᵐ y ∂timeVelocityVolumeOn O, 0 ≤ f y)
    (hrho : ∀ y, 0 ≤ rho y) :
    0 ≤ parabolicConvolution f rho z := by
  change 0 ≤ ∫ y, f y * rho (z - y)
  apply integral_nonneg_of_ae
  have hnonneg' : ∀ᵐ y ∂volume, y ∈ O → 0 ≤ f y := by
    change ∀ᵐ y ∂volume.restrict O, 0 ≤ f y at hnonneg
    exact (ae_restrict_iff' hO).mp hnonneg
  filter_upwards [hnonneg'] with y hy
  change 0 ≤ f y * rho (z - y)
  by_cases hyO : y ∈ O
  · exact mul_nonneg (hy hyO) (hrho (z - y))
  · have hzero : rho (z - y) = 0 := by
      by_contra hne
      exact hyO (hsupport hne)
    simp [hzero]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Filter

/- An a.e. local equation for a global selected jet gives the eventual
pointwise residual equation on a compact carrier. -/
theorem eventually_residual_equation_of_ae_on
    {d Aext K O p}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (g : ParabolicW12Function d Set.univ p) (hp : 1 ≤ p)
    (heq : g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt Aext z) (g.velocityHessian z)) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue g n) z =
        weakEquationMollificationResidual Aext g n z := by
  filter_upwards [(eventually_translated_parabolicMollifier_support_subset d K O hK hO hKO)] with n hn
  intro z hz
  have hconv := parabolicConvolution_eq_of_ae_eq_on_support hO.measurableSet z (hn z hz) heq
  calc
    parabolicOperator (parabolicMollifyCoefficient Aext n)
        (parabolicMollifiedValue g n) z =
        parabolicConvolution g.timeDeriv (parabolicMollifier d n) z -
          matrixContraction (coefficientAt (parabolicMollifyCoefficient Aext n) z)
            (parabolicMollifiedHessian g n z) := by
        have _h_inl_15 : timeDerivative (parabolicMollifiedValue g n) =
      parabolicConvolution g.timeDeriv (parabolicMollifier d n) := by
            simpa only [parabolicMollifiedValue] using
              g.timeDerivative_convolution hp (parabolicMollifier d n)
                (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)



        have _h_inl_14 : velocityHessian (parabolicMollifiedValue g n) = parabolicMollifiedHessian g n := by
          funext z
          ext i j
          exact congrFun
            (g.velocityHessian_convolution hp (parabolicMollifier d n)
              (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n) i j) z
        rw [parabolicOperator_apply, _h_inl_15,
          _h_inl_14]
    _ = weakEquationMollificationResidual Aext g n z := by
        rw [hconv]
        rfl

/- A global selected jet which is a.e. nonnegative on an open neighborhood
of a compact carrier has eventually pointwise nonnegative mollifications
there. -/
theorem eventually_nonnegative_parabolicMollifiedValue_of_ae_nonnegative_on
    {d K O p}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (g : ParabolicW12Function d Set.univ p)
    (hnonneg : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ g.toFun z) :
    ∀ᶠ n in atTop, ∀ z ∈ K, 0 ≤ parabolicMollifiedValue g n z := by
  filter_upwards [(eventually_translated_parabolicMollifier_support_subset d K O hK hO hKO)] with n hn
  intro z hz
  exact parabolicConvolution_nonneg_of_ae_nonneg_on_support hO.measurableSet z
    (hn z hz) hnonneg (parabolicMollifier_nonneg d n)

end HypoellipticAleksandrov.Parabolic
