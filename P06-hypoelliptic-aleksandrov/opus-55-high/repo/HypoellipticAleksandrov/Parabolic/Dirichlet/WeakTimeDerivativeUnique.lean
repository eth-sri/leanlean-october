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

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T} {u : ReverseTimeL2V hΩ T}

private theorem memLp_two_weakDerivativePairing_sub
    
    (g g' : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) :
    MemLp (fun tau => (g tau) v - (g' tau) v)
      (2 : ℝ≥0∞) (reverseTimeVolume T) := by
  simpa only [Pi.sub_def, ContinuousLinearMap.apply_apply] using
    ((MeasureTheory.Lp.memLp g).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℝ v)).sub
      ((MeasureTheory.Lp.memLp g').continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℝ v))

private theorem integral_weakDerivativePairing_sub_eq_zero
     {g g' : ReverseTimeL2VStar hΩ T}
    (hg : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hg' : HasGelfandWeakTimeDerivative hΩ T hT u g')
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (∫ tau, ((g tau) v - (g' tau) v) * eta tau ∂reverseTimeVolume T) = 0 := by
  obtain ⟨_, hright, hidentity⟩ := hg v eta
  obtain ⟨_, hright', hidentity'⟩ := hg' v eta
  have hrightEq :
      (∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) =
        ∫ tau, (g' tau) v * eta tau ∂reverseTimeVolume T := by
    simp_all
  calc
    (∫ tau, ((g tau) v - (g' tau) v) * eta tau ∂reverseTimeVolume T) =
        ∫ tau, ((g tau) v * eta tau - (g' tau) v * eta tau) ∂reverseTimeVolume T := by
          apply integral_congr_ae
          filter_upwards with tau
          linarith
    _ = (∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) -
        ∫ tau, (g' tau) v * eta tau ∂reverseTimeVolume T :=
          integral_sub hright hright'
    _ = 0 := by simp_all

/-- A fixed reverse-time curve has at most one Gelfand weak time derivative,
as an `L²(V*)` equivalence class. -/
theorem HasGelfandWeakTimeDerivative.unique
    
    {g g' : ReverseTimeL2VStar hΩ T}
    (hg : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hg' : HasGelfandWeakTimeDerivative hΩ T hT u g') :
    g = g' := by
  letI  :=
    h10HilbertGraphSeparableSpace hΩ
  let q  :=
    TopologicalSpace.denseSeq (H10HilbertGraph hΩ)
  have hqDense : DenseRange q :=
    TopologicalSpace.denseRange_denseSeq _
  have hpairAE : ∀ n : ℕ, ∀ᵐ tau ∂reverseTimeVolume T,
      (g tau) (q n) = (g' tau) (q n) := by
    intro n
    filter_upwards [ae_eq_zero_of_memLp_two_integral_reverseTimeScalarTest T
      (memLp_two_weakDerivativePairing_sub g g' _)
      (fun eta => integral_weakDerivativePairing_sub_eq_zero hg hg' (q n) eta)] with tau htau
    exact sub_eq_zero.mp htau
  have hpairAll  :=
    ae_all_iff.mpr hpairAE
  have hdualAE : ∀ᵐ tau ∂reverseTimeVolume T, g tau = g' tau := by
    filter_upwards [hpairAll] with tau htau
    apply ContinuousLinearMap.coeFn_injective
    exact Continuous.ext_on hqDense (g tau).continuous (g' tau).continuous (by
      aesop)
  aesop

end HypoellipticAleksandrov.Parabolic.Dirichlet
