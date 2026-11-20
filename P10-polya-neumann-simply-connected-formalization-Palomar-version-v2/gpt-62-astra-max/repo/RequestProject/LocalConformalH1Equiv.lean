module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalMass
public import RequestProject.LocalConformalTests
public import Mathlib.Analysis.Normed.Operator.Banach
public import RequestProject.PlanarNotation

/-!
# The actual H¹ equivalence for supplied conformal coordinates

The pullback is the existing bounded map between the genuine weak-gradient H¹
spaces. Its inverse is constructed here: the mass change-of-variables identity
and the conformal gradient identity give a reverse norm bound, hence closed
range; physical inverse-coordinate tests put every smooth disk restriction in
that range, hence density and surjectivity.

All coordinate and inverse data are supplied explicitly. This file does not
construct an initial conformal map or assume surjectivity of the pullback.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

section NormBound

section

variable (Φ : ControlledDiskMap) (u : NeumannH1 Φ.domain)

/-- The physical H¹ norm is bounded by the norm of the actual disk pullback.
The multiplier constant is the genuine bound on the conformal Jacobian root. -/
theorem localConformalH1Pullback_reverse_norm_sq :
    ‖u‖ ^ 2 ≤ max (Φ.K ^ 2) 1 * ‖Φ.h1Pullback Φ.lipschitzDomain u‖ ^ 2 := by
  let v := Φ.h1Pullback Φ.lipschitzDomain u
  have hK0  := (norm_nonneg _).trans
    (Φ.deriv_upper 0 (by simp))
  have hm := norm_sq_localConformalMassPullback Φ u
  have hg := localConformalH1Pullback_gradient_energy Φ u
  have hmul : ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u‖ ≤
      Φ.K * ‖h1Value unitDisk v‖ := by
    change ‖lpBoundedMultiplier (localConformalMassDensity Φ.map)
      (localConformalMassDensity_aemeasurable Φ)
      (localConformalMassDensity_ae_bound Φ.map Φ.deriv_upper)
      (h1Value unitDisk v)‖ ≤ _
    exact norm_lpBoundedMultiplier_le _ _ _ _
  have hmulSq : ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u‖ ^ 2 ≤
      Φ.K ^ 2 * ‖h1Value unitDisk v‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).2 hmul
  have hgrad0 : 0 ≤ ∑ i : Fin 2, ‖h1Gradient unitDisk i v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ = ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u‖ ^ 2 +
        ∑ i : Fin 2, ‖h1Gradient unitDisk i v‖ ^ 2 := by
      rw [h1_norm_sq, hm]
      exact congrArg (fun t => ‖h1Value Φ.domain u‖ ^ 2 + t) hg.symm
    _ ≤ Φ.K ^ 2 * ‖h1Value unitDisk v‖ ^ 2 +
        ∑ i : Fin 2, ‖h1Gradient unitDisk i v‖ ^ 2 :=
      add_le_add hmulSq le_rfl
    _ ≤ max (Φ.K ^ 2) 1 * ‖h1Value unitDisk v‖ ^ 2 +
        max (Φ.K ^ 2) 1 * (∑ i : Fin 2, ‖h1Gradient unitDisk i v‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_right (Φ.K ^ 2) 1) hgrad0
    _ = _ := by
      rw [h1_norm_sq]
      ring

/-- A concrete bounded-below estimate for the actual pullback. -/
theorem localConformalH1Pullback_reverse_norm :
    ‖u‖ ≤ Real.sqrt (max (Φ.K ^ 2) 1) * ‖Φ.h1Pullback Φ.lipschitzDomain u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (le_trans zero_le_one (le_max_right (Φ.K ^ 2) 1))]
  exact localConformalH1Pullback_reverse_norm_sq Φ u

theorem localConformalH1Pullback_antilipschitz :
    AntilipschitzWith (Real.toNNReal (Real.sqrt (max (Φ.K ^ 2) 1)))
      (Φ.h1Pullback Φ.lipschitzDomain) := by
  apply (Φ.h1Pullback Φ.lipschitzDomain).antilipschitz_of_bound
  intro u
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact localConformalH1Pullback_reverse_norm Φ u

theorem localConformalH1Pullback_injective :
    Function.Injective (Φ.h1Pullback Φ.lipschitzDomain) :=
  (localConformalH1Pullback_antilipschitz Φ).injective

theorem localConformalH1Pullback_isClosed_range :
    IsClosed (Set.range (Φ.h1Pullback Φ.lipschitzDomain)) :=
  (localConformalH1Pullback_antilipschitz Φ).isClosed_range
    (Φ.h1Pullback Φ.lipschitzDomain).uniformContinuous

end

end NormBound

section DenseRange

section

variable (Φ : ConformalDiskMap) (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map)
    (hsource : closedDisk ⊆ e.source) (hes : ContDiffOn ℝ ∞ e.symm e.target)
include he hes hsource

/-- Every genuine smooth disk restriction is the pullback of a physical test. -/
theorem smoothTraceH1_mem_localConformalH1Pullback_range (φ : smoothTraceTests) :
    smoothTraceH1 unitDisk φ ∈
      Set.range (Φ.h1Pullback Φ.lipschitzDomain) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test Φ e he hsource hes φ.property.1
  refine ⟨smoothTraceH1 Φ.domain f, hp.trans ?_⟩
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  exact diskHarmonicCutoff_eq_closedDisk φ (ball_subset_closedBall hz)

/-- Density follows from exact physical inverse-coordinate tests, rather than
from an assumed surjectivity statement. -/
theorem localConformalH1Pullback_denseRange :
    DenseRange (Φ.h1Pullback Φ.lipschitzDomain) := by
  have hsub : Set.range (smoothTraceH1Lin isOpen_ball) ⊆
      Set.range (Φ.h1Pullback Φ.lipschitzDomain) := by
    rintro _ ⟨φ, rfl⟩
    exact smoothTraceH1_mem_localConformalH1Pullback_range Φ e he hsource hes φ
  intro v
  exact closure_mono hsub
    ((denseRange_smoothTraceH1Lin unitDisk_bounded isLipschitzDomain_unitDisk) v)

end

end DenseRange

section Equivalence

section

variable (Φ : DiskCoordinates)

theorem localConformalH1Pullback_surjective :
    Function.Surjective (Φ.h1Pullback Φ.lipschitzDomain) := by
  intro v
  have hv := localConformalH1Pullback_denseRange Φ Φ.chart Φ.chart_eq Φ.source Φ.smoothInverse v
  rw [(localConformalH1Pullback_isClosed_range Φ).closure_eq]
    at hv
  exact hv

/-- The supplied-map H¹ equivalence; its forward map is the actual pullback. -/
def DiskCoordinates.h1Equiv :
    NeumannH1 Φ.domain ≃L[ℂ] NeumannH1 unitDisk :=
  ContinuousLinearEquiv.ofBijective (Φ.h1Pullback Φ.lipschitzDomain)
    (LinearMap.ker_eq_bot.mpr
      (localConformalH1Pullback_injective Φ))
    (LinearMap.range_eq_top.mpr
      (localConformalH1Pullback_surjective Φ))

/-- The actual continuous inverse, taking a disk H¹ vector to its physical vector. -/
def DiskCoordinates.h1Pushforward :
    NeumannH1 unitDisk →L[ℂ] NeumannH1 Φ.domain :=
  Φ.h1Equiv.symm.toContinuousLinearMap

@[simp] theorem localConformalH1Pullback_pushforward
    (v : NeumannH1 unitDisk) :
    Φ.h1Pullback Φ.lipschitzDomain
      (Φ.h1Pushforward v) = v :=
  Φ.h1Equiv.apply_symm_apply v

end

end Equivalence

end PolyaNeumann

end
