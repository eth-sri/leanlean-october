module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Support
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator

section
open private HypoellipticAleksandrov.Parabolic.Dirichlet.hasCompactSupport_timeVelocity_slice from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10Commutator
private alias _sharedProof_353_0 := HypoellipticAleksandrov.Parabolic.Dirichlet.hasCompactSupport_timeVelocity_slice
end


/-! # Compact cutoff support and integrability on local cylinders

Multiplication by an interior compact cutoff makes locally continuous quantities globally
integrable, and fixed-time slices retain compact support inside the spatial carrier.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology

variable {d : ℕ}

section
variable {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)

include hU
/-- A continuous local field times an interior compact cutoff is globally integrable. -/
theorem integrable_local_cutoff_mul   (f χ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContinuousOn f U)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    Integrable (fun z => f z * χ z) := (Continuous.integrable_of_hasCompactSupport
  (ContinuousOn.continuous_of_tsupport_subset (ContinuousOn.mul hf (Continuous.continuousOn hχ)) hU
    (LE.le.trans tsupport_mul_subset_right hsub))
  (HasCompactSupport.mul_left hc))

/-- Squared interior cutoffs also globalize continuous local integrands. -/
theorem integrable_local_cutoff_square_mul   (f ρ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContinuousOn f U)
    (hρ : Continuous ρ) (hc : HasCompactSupport ρ) (hsub : tsupport ρ ⊆ U) :
    Integrable (fun z => f z * ρ z ^ 2) := (integrable_local_cutoff_mul hU f (fun z => ρ z ^ 2) hf (Continuous.pow hρ 2)
  (Eq.mpr (id (congrArg (fun _a => HasCompactSupport _a) (funext fun z => pow_two (ρ z))))
    (HasCompactSupport.mul_left hc))
  (LE.le.trans
    (Eq.mpr (id (congrFun' (congrArg LE.le (congrArg tsupport (funext fun z => pow_two (ρ z)))) (tsupport ρ)))
      tsupport_mul_subset_right)
    hsub))
end


variable (χ : HypoellipticAleksandrov.Parabolic.ScalarField d)

/-- A fixed-time slice of a compact spacetime cutoff has compact spatial support. -/
theorem hasCompactSupport_local_cutoff_time_slice
     (hc : HasCompactSupport χ) (t : ℝ) :
    HasCompactSupport (fun y => χ (t, y)) := (_sharedProof_353_0 χ hc t)


/-- The support of a fixed-time cutoff slice stays in the spatial carrier. -/
theorem tsupport_local_cutoff_time_slice_subset
     {a T : ℝ} {O : PDE.VelocityRegion d}
    (hsub : tsupport χ ⊆ Ioo a T ×ˢ O) (t : ℝ) :
    tsupport (fun y => χ (t, y)) ⊆ O := by
  have hpre : tsupport (fun y => χ (t, y)) ⊆
      (fun y => (t, y)) ⁻¹' tsupport χ := by
    apply closure_minimal
    · intro y hy
      exact subset_tsupport χ hy
    · exact (isClosed_tsupport χ).preimage (continuous_const.prodMk continuous_id)
  exact fun y hy => (hsub (hpre hy)).2

/-- Spatial slice derivatives vanish outside the actual spacetime support. -/
theorem scalarSpatialGradient_eq_zero_of_notMem_tsupport
    (ρ : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) (i : Fin d)
    (hz : z ∉ tsupport ρ) : scalarSpatialGradient ρ z i = 0 := by
  have heq : ρ =ᶠ[𝓝 z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hs : (fun y => ρ (z.1, y)) =ᶠ[𝓝 z.2] fun _ => 0 :=
    heq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hd := (hs.fderiv (𝕜 := ℝ)).self_of_nhds
  change fderiv ℝ (fun y => ρ (z.1, y)) z.2 (PDE.basisVec i) = 0
  rw [hd]
  simp only [fderiv_const_apply, zero_apply]

end HypoellipticAleksandrov.Parabolic.LocalHolder
