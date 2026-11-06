module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.Positivity

/-!
# Bounded approximate identities on finite-measure regions

These analytic helpers use actual normalized smooth kernels. They are independent
of the Appendix C profile constructor and apply to measurable coefficients.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ENNReal

/-- Native spatial volume is the product of the two coordinate Lebesgue Haar measures. -/
instance nativeSpatialVolume_isAddHaarMeasure (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec d × PDE.Vec d)) := Measure.prod.instIsAddHaarMeasure _ _

/-- Bounded almost-everywhere convergence implies finite-exponent norm convergence. -/
theorem bounded_convergence_eLpNorm {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (F : ℕ → X → ℝ) (hF : ∀ n, AEStronglyMeasurable (F n) ν)
    (C : ℝ) (hbound : ∀ n, ∀ᵐ x ∂ν, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p ν) atTop (𝓝 0) := by
  have hpow  := ENNReal.toReal_pos hp0 hp
  have hi : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_lintegral_of_dominated_convergence'
      (μ := ν) (F := fun n x => ‖F n x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal C ^ p.toReal)
      (fun n => (hF n).enorm.pow_const p.toReal) ?_ ?_ ?_
    · simp_all
    · intro n
      filter_upwards [hbound n] with x hx
      apply ENNReal.rpow_le_rpow _ hpow.le
      simpa only [ofReal_norm] using! ENNReal.ofReal_le_ofReal hx
    · simp only [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpow.le
        ENNReal.ofReal_ne_top) (measure_ne_top ν Set.univ)
    · filter_upwards [hlim] with x hx
      have hn : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, enorm_zero] using!
          (continuous_enorm.tendsto _).comp hx
      simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos hpow] using!
        (ENNReal.continuous_rpow_const (y := p.toReal).tendsto _).comp hn
  have hr := (ENNReal.continuous_rpow_const (y := 1 / p.toReal).tendsto
    _).comp hi
  have hresult : Tendsto (fun n =>
      (∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal)) atTop (𝓝 0) := by
    aesop
  apply hresult.congr
  intro n
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hF n)).symm

section Kernels
variable {G : Type*} [NormedAddCommGroup G]

/-- A smooth spatial kernel with inner radius half its specified outer radius. -/
def spatialMollifier (h : ℝ) (hh : 0 < h) : ContDiffBump (0 : G) where
  rIn := h / 2
  rOut := h
  rIn_pos := half_pos hh
  rIn_lt_rOut := half_lt_self hh

/-- A concrete family of kernels at scales `1/(n+1)`. -/
def standardMollifierSequence (n : ℕ) : ContDiffBump (0 : G) :=
  spatialMollifier (1 / ((n : ℝ) + 1)) (by positivity)

/-- The concrete kernels have radii tending to zero. -/
theorem standardMollifierSequence_rOut_tendsto :
    Tendsto (fun n => (standardMollifierSequence (G := G) n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Uniform inner-to-outer radius ratio for the concrete kernels. -/
theorem standardMollifierSequence_radius_ratio (n : ℕ) :
    (standardMollifierSequence (G := G) n).rOut ≤
      2 * (standardMollifierSequence (G := G) n).rIn := by
  change 1 / (n + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2)
  linarith

end Kernels

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
   [Measure.IsAddHaarMeasure (volume : Measure G)]

/-- Spatial smoothing by an actual normalized bump kernel. -/
def spatialMollify (φ : ContDiffBump (0 : G)) (g : G → ℝ) : G → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] g

variable (φ : ContDiffBump (0 : G)) (g : G → ℝ)

/-- Bounded input gives the same uniform bound after normalized convolution. -/
theorem spatialMollify_norm_le 
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) (x : G) : ‖spatialMollify φ g x‖ ≤ C := by
  have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0)) hC
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hg
    (fun y _ => by simp_all)
  aesop

/-- Spatial convolution is smooth; this does not assert joint time smoothness. -/
theorem spatialMollify_contDiff 
    (hg : LocallyIntegrable g volume) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialMollify φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _
    φ.contDiff_normed hg

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
