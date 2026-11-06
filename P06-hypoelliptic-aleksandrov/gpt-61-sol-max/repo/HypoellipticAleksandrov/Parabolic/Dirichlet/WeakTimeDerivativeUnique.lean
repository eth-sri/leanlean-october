module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDistribution
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevSeparable

/-!
# Uniqueness of Gelfand weak time derivatives

This module proves quotient-valued uniqueness of the weak time derivative of
a fixed reverse-time curve.  The proof uses scalar distribution separation on
a countable dense set of spatial test vectors, then continuity of the dual
functionals.  It does not assert uniqueness of PDE weak solutions.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {hΩ : IsOpen Ω} {T : ℝ}

private theorem memLp_two_weakDerivativePairing_sub

    (g g' : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) :
    MemLp (fun tau => (g tau) v - (g' tau) v)
      (2 ) (reverseTimeVolume T) := (MemLp.sub (MemLp.continuousLinearMap_comp (Lp.memLp g) ((ContinuousLinearMap.apply ℝ ℝ) v))
  (MemLp.continuousLinearMap_comp (Lp.memLp g') ((ContinuousLinearMap.apply ℝ ℝ) v)))

variable {hT : 0 < T} {u : ReverseTimeL2V hΩ T} {g g' : ReverseTimeL2VStar hΩ T} (hg : HasGelfandWeakTimeDerivative hΩ T hT u g) (hg' : HasGelfandWeakTimeDerivative hΩ T hT u g')

include hg hg'
private theorem integral_weakDerivativePairing_sub_eq_zero

    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (∫ tau, ((g tau) v - (g' tau) v) * eta tau ∂reverseTimeVolume T) = 0 := by
  obtain ⟨_, hright, hidentity⟩ := hg v eta
  obtain ⟨_, hright', hidentity'⟩ := hg' v eta
  have hrightEq :
      (∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) =
        ∫ tau, (g' tau) v * eta tau ∂reverseTimeVolume T := by
    calc
      (∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) =
          -(∫ tau,
            inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau
            ∂reverseTimeVolume T) := by
              simpa only [neg_neg] using (congrArg Neg.neg hidentity).symm
      _ = ∫ tau, (g' tau) v * eta tau ∂reverseTimeVolume T := by
            simpa only [neg_neg] using congrArg Neg.neg hidentity'
  calc
    (∫ tau, ((g tau) v - (g' tau) v) * eta tau ∂reverseTimeVolume T) =
        ∫ tau, ((g tau) v * eta tau - (g' tau) v * eta tau) ∂reverseTimeVolume T := by
          apply integral_congr_ae
          filter_upwards with tau
          rw [sub_mul]
    _ = (∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) -
        ∫ tau, (g' tau) v * eta tau ∂reverseTimeVolume T :=
          integral_sub hright hright'
    _ = 0 := by rw [hrightEq, sub_self]

/-- A fixed reverse-time curve has at most one Gelfand weak time derivative,
as an `L²(V*)` equivalence class. -/
theorem HasGelfandWeakTimeDerivative.unique
      :
    g = g' := by
  letI : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) :=
    h10HilbertGraphSeparableSpace hΩ
  let q : ℕ → H10HilbertGraph hΩ :=
    TopologicalSpace.denseSeq (H10HilbertGraph hΩ)


  have hpairAll  :=
    ae_all_iff.mpr (by
        intro n
        filter_upwards [ae_eq_zero_of_memLp_two_integral_reverseTimeScalarTest T
          (memLp_two_weakDerivativePairing_sub g g' (q n))
          (fun eta => integral_weakDerivativePairing_sub_eq_zero hg hg' (q n) eta)] with tau htau
        exact sub_eq_zero.mp htau)

  exact MeasureTheory.Lp.ext (by
      filter_upwards [hpairAll] with tau htau
      apply ContinuousLinearMap.coeFn_injective
      exact Continuous.ext_on (TopologicalSpace.denseRange_denseSeq (H10HilbertGraph hΩ)) (g tau).continuous (g' tau).continuous (by
        rintro _ ⟨n, rfl⟩
        exact htau n))

end HypoellipticAleksandrov.Parabolic.Dirichlet
