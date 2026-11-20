module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalMass
public import RequestProject.LocalConformalTests
public import Mathlib.Analysis.Normed.Operator.Banach

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

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "D" => ball (0 : ℂ) 1
local notation "Ω" => F '' D
local notation "K" => coords.derivativeBound

/-- The physical H¹ norm is bounded by the norm of the actual disk pullback.
The multiplier constant is the genuine bound on the conformal Jacobian root. -/
theorem localConformalH1Pullback_reverse_norm_sq
    (u : NeumannH1 Ω) :
    ‖u‖ ^ 2 ≤ max (K ^ 2) 1 * ‖coords.pullback u‖ ^ 2 := by
  let v := coords.pullback u
  have hm := norm_sq_localConformalMassPullback coords u
  have hg := localConformalH1Pullback_gradient_energy coords u
  have hmul : ‖localConformalMassPullback coords u‖ ≤
      K * ‖h1Value D v‖ :=
    norm_lpBoundedMulLin_le _ (localConformalMassDensity_aemeasurable F)
      (localConformalMassDensity_ae_bound coords) _
  have hK0 := (norm_nonneg _).trans (coords.upper 0 (by simp))
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).mpr hmul
  rw [mul_pow] at hsq
  rw [h1_norm_sq _ u, h1_norm_sq _ v, ← hm, ← hg, mul_add]
  refine add_le_add (hsq.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))) ?_
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right (K ^ 2) 1)
    (Finset.sum_nonneg fun _ _ => sq_nonneg ‖h1Gradient D _ v‖)

theorem localConformalH1Pullback_antilipschitz :
    AntilipschitzWith (Real.toNNReal (Real.sqrt (max (K ^ 2) 1)))
      (coords.pullback) := by
  apply (coords.pullback).antilipschitz_of_bound
  intro u
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (le_trans zero_le_one (le_max_right (K ^ 2) 1))]
  exact localConformalH1Pullback_reverse_norm_sq coords u

theorem localConformalH1Pullback_isClosed_range :
    IsClosed (Set.range (coords.pullback)) :=
  (localConformalH1Pullback_antilipschitz coords).isClosed_range
    (coords.pullback).uniformContinuous

/-- Every genuine smooth disk restriction is the pullback of a physical test. -/
theorem smoothTraceH1_mem_localConformalH1Pullback_range (φ : smoothTraceTests) :
    smoothTraceH1 D φ ∈
      Set.range (coords.pullback) := by
  obtain ⟨f, _, hp⟩ := exists_localConformal_physical_test coords φ.property.1
  refine ⟨smoothTraceH1 Ω f, hp.trans ?_⟩
  apply smoothTraceH1_eq_of_eqOn isOpen_ball
  intro z hz
  exact diskHarmonicCutoff_eq_closedDisk (φ : ℂ → ℂ) (ball_subset_closedBall hz)

/-- Density follows from exact physical inverse-coordinate tests, rather than
from an assumed surjectivity statement. -/
theorem localConformalH1Pullback_denseRange :
    DenseRange (coords.pullback) := by
  have hsub : Set.range (smoothTraceH1Lin isOpen_ball) ⊆
      Set.range (coords.pullback) := by
    rintro _ ⟨φ, rfl⟩
    exact smoothTraceH1_mem_localConformalH1Pullback_range coords φ
  intro v
  exact closure_mono hsub
    ((denseRange_smoothTraceH1Lin unitDisk_bounded isLipschitzDomain_unitDisk) v)

theorem localConformalH1Pullback_surjective :
    Function.Surjective (coords.pullback) := by
  intro v
  have hv := localConformalH1Pullback_denseRange coords v
  rw [(localConformalH1Pullback_isClosed_range coords).closure_eq]
    at hv
  assumption

/-- The supplied-map H¹ equivalence; its forward map is the actual pullback. -/
def localConformalH1Equiv :
    NeumannH1 Ω ≃L[ℂ] NeumannH1 D :=
  ContinuousLinearEquiv.ofBijective (coords.pullback)
    (LinearMap.ker_eq_bot.mpr
      (localConformalH1Pullback_antilipschitz coords).injective)
    (LinearMap.range_eq_top.mpr
      (localConformalH1Pullback_surjective coords))


/-- The actual continuous inverse, taking a disk H¹ vector to its physical vector. -/
def localConformalH1Pushforward :
    NeumannH1 D →L[ℂ] NeumannH1 Ω :=
  (localConformalH1Equiv coords).symm.toContinuousLinearMap

@[simp] theorem localConformalH1Pullback_pushforward
    (v : NeumannH1 D) :
    coords.pullback
      (localConformalH1Pushforward coords v) = v :=
  (localConformalH1Equiv coords).apply_symm_apply v


end PolyaNeumann

end
