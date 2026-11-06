module
public import GuthMaynard.Improvement.ShortTypeICount
public import GuthMaynard.Improvement.WeakTypeIICount
public import GuthMaynard.Improvement.ShortDetectorCounting
public import MathCollab.Density.DensityDyadicSummation
public import HalfLossTypeIISlab
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter Set MathCollab.Density
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Actual Type-II zero representatives from the ordinary fourth moment. -/
theorem weak_short_typeII_zero_slab_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ (σ : ℝ) (R : Finset ℂ),
      9/13 ≤ σ → R ⊆ zetaZeroFinset σ H (2*H) →
      (R.image Complex.im).card = R.card → oneSeparated (R.image Complex.im) →
      (∀ ρ ∈ R, (1/3:ℝ) ≤
        ‖detectorIntegral ρ (2*H^((100:ℝ)⁻¹)) (H^(1/2:ℝ))‖) →
      (R.card:ℝ) ≤ C*H^(2-2*σ+1/25+ε) := by pm_3945 weak_short_typeII_count

/-- The Type-II exponent fits the target throughout the closed sigma window. -/
theorem weak_short_typeII_exponent_le {σ : ℝ} (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 5/7) :
    2-2*σ+1/25 ≤ shortDensityExponent σ := by
  pm_1115
  rw [shortDensityExponent,le_div_iff₀ hd]
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (show 7*σ-5 ≤ 0 by linarith)
    (show 28*σ-33 ≤ 0 by linarith)]

/-- Uniform actual slab density using the weaker, proved moment estimate.
Both separated branch estimates, contour detection and analytic multiplicity
restoration are proved dependencies. -/
theorem short_slab_density
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ σ : ℝ,
      9/13 ≤ σ → σ ≤ 5/7 →
      (zetaSlabCount σ H (2*H):ℝ) ≤ C*H^(shortDensityExponent σ+ε) := by
  pm_6200 short_typeI_zero_slab_count
  pm_4605
  pm_178 hH1 H hH0
  have hb := hr σ (CI*H^(shortDensityExponent σ+ε/2))
    (CII*H^(shortDensityExponent σ+ε/2)) hσ (fun R hR hc hs hl => hi σ R hσ hσ' hR hc hs hl) (by
      intro R hR hc hs hl
      exact (hii σ R hσ hR hc hs hl).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH1
          (by linarith [weak_short_typeII_exponent_le hσ hσ'])) hCII.le))
  pm_1427
  calc
    _ ≤ C₀*Real.log (2*H)*(CI*H^(shortDensityExponent σ+ε/2)+CII*H^(shortDensityExponent σ+ε/2)) := hb
    _ ≤ C₀*(D*H^(ε/2))*(CI*H^(shortDensityExponent σ+ε/2)+CII*H^(shortDensityExponent σ+ε/2)) := by gcongr
    _ = (C₀*(CI+CII)*D)*(H^(ε/2)*H^(shortDensityExponent σ+ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hH0]; congr 2; ring

/-- All actual zeros with analytic multiplicity and both signs. The audited
fixed-sigma dyadic summation is reused, so this constant may depend on sigma. -/
theorem short_density
    {σ ε : ℝ} (hσ : 9/13 ≤ σ) (hσ' : σ ≤ 5/7) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(18*(1-σ)/(7*σ+3)+ε) := by
  obtain ⟨C,hC,hslab⟩ := short_slab_density hε
  have hp : 0 < shortDensityExponent σ+ε := by
    have he := (short_density_scale_bounds hσ hσ').2.2.2.2.1
    linarith
  pm_6733

end GuthMaynard.Improvement
