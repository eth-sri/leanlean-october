module

public import RequestProject.LpBoundedMultiplier
public import RequestProject.LocalConformalGradient
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The physical mass form in given conformal coordinates

The Jacobian square root multiplies the genuine H¹ pullback in disk L².
Change of variables proves its mass norm identity on smooth restrictions;
density and complex polarization prove the full weak mass pairing.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped InnerProductSpace

def localConformalMassDensity (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (‖fderiv ℝ F z 1‖ : ℝ)

theorem localConformalMassDensity_aemeasurable (F : ℂ → ℂ) :
    AEStronglyMeasurable (localConformalMassDensity F) (volume.restrict (ball 0 1)) :=
  (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ F (1 : ℂ)).norm).aestronglyMeasurable

theorem localConformalMassDensity_ae_bound {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    ∀ᵐ z ∂volume.restrict (ball 0 1), ‖localConformalMassDensity F z‖ ≤ coords.derivativeBound := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  simpa [localConformalMassDensity] using coords.upper z hz

theorem norm_sq_L2_eq_integral {U : Set ℂ} (v : L2 U) :
    ‖v‖ ^ 2 = ∫ z in U, ‖(v : ℂ → ℂ) z‖ ^ 2 := by simpa using norm_sq_toLp_eq_integral (Lp.memLp v)

section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "D" => ball (0 : ℂ) 1
local notation "Ω" => F '' D

def localConformalMassMultiplier : L2 D →L[ℂ] L2 D :=
  lpBoundedMultiplier (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable F)
    (localConformalMassDensity_ae_bound coords)

theorem localConformalMassMultiplier_ae (v : L2 D) :
    (localConformalMassMultiplier coords v : ℂ → ℂ) =ᵐ[volume.restrict D]
      fun z => localConformalMassDensity F z * v z := lpBoundedMultiplier_ae _ _ _ v

def localConformalMassPullback : NeumannH1 Ω →L[ℂ] L2 D :=
  (localConformalMassMultiplier coords).comp
    ((h1Value D).comp (coords.pullback))

theorem localConformalMassPullback_smooth_ae (f : smoothTraceTests) :
    (localConformalMassPullback coords (smoothTraceH1 Ω f) : ℂ → ℂ)
      =ᵐ[volume.restrict D] fun z => localConformalMassDensity F z * f (F z) := by
  change (localConformalMassMultiplier coords
    (h1Value D (coords.pullback (smoothTraceH1 Ω f))) : ℂ → ℂ) =ᵐ[_] _
  rw [localConformalH1Pullback_smooth coords.one_lt_radius F coords.smooth coords.bounded
    coords.lipschitz coords.holomorphic coords.injOn coords.lower, h1Value_smoothTraceH1]
  let g := smoothDiskCompositionLin coords.one_lt_radius F coords.smooth f
  have hg := smoothTraceTests_memLp D g
  filter_upwards [localConformalMassMultiplier_ae coords (hg.toLp g),
    hg.coeFn_toLp, ae_restrict_mem measurableSet_ball] with z hm hv hz
  rw [hm, hv, smoothDiskCompositionLin_eq_closedDisk coords.one_lt_radius F coords.smooth f (ball_subset_closedBall hz)]

theorem norm_sq_localConformalMassPullback
    (u : NeumannH1 (Ω)) :
    ‖localConformalMassPullback coords u‖ ^ 2 =
      ‖h1Value (Ω) u‖ ^ 2 := by
  refine (denseRange_smoothTraceH1Lin coords.bounded coords.lipschitz).induction_on
    (p := fun v => ‖localConformalMassPullback coords v‖ ^ 2 =
      ‖h1Value (Ω) v‖ ^ 2) u ?_ ?_
  · exact isClosed_eq ((localConformalMassPullback coords).continuous.norm.pow 2)
      ((h1Value (Ω)).continuous.norm.pow 2)
  · intro f
    change ‖localConformalMassPullback coords (smoothTraceH1 Ω f)‖ ^ 2 =
      ‖h1Value Ω (smoothTraceH1 Ω f)‖ ^ 2
    rw [norm_sq_L2_eq_integral, h1Value_smoothTraceH1, norm_sq_toLp_eq_integral,
      localConformal_integral_image isOpen_ball coords.holomorphic coords.injOn]
    apply integral_congr_ae
    filter_upwards [localConformalMassPullback_smooth_ae coords f,
      ae_restrict_mem measurableSet_ball] with z hza hz
    simp [hza, localConformalMassDensity, coords.real_fderiv_apply (ball_subset_closedBall hz),
      norm_mul, mul_pow]

theorem localConformalMassPullback_inner
    (u v : NeumannH1 (Ω)) :
    ⟪localConformalMassPullback coords u,
      localConformalMassPullback coords v⟫_ℂ =
      ⟪h1Value (Ω) u, h1Value (Ω) v⟫_ℂ := by
  exact inner_eq_of_linear_norm_sq
    (localConformalMassPullback coords).toLinearMap
    (h1Value (Ω)).toLinearMap
    (norm_sq_localConformalMassPullback coords) u v

end

end PolyaNeumann

end
