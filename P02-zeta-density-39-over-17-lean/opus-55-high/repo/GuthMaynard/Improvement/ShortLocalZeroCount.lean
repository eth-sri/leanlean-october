module
/- Adapted from audited Density.LocalZeroCount at eff263d7, whose Jensen
 proof derives from Scott McColm (MIT). The same actual zero count and
 multiplicities are retained; a radius3/2 disk also covers Re(rho)>=3/5. -/
public import MathCollab.Density.LocalZeroCount
import WeylPort.Analytic.RealLaplace

public section
open Complex Filter MeasureTheory MathCollab.Density
open scoped Topology
open MathCollab.Density.ZetaGrowth
namespace GuthMaynard.Improvement

theorem short_zeta_unit_bin_sum_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 3 / 5 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        zetaMultiplicity ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7/4 : ℝ) / (3/2 : ℝ)) := by pf_5 7 5

/-- A single logarithmic multiplicity constant for every actual zero bin.
Both the large-height Jensen estimate and the bounded-height range are proved. -/
theorem short_zeta_local_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 9/13 ≤ σ → 2 ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ C*Real.log (2*T) := by pf_22 9 13 short_zeta_unit_bin_sum_le_jensen

/-- Unconditional logarithmic restoration of all analytic multiplicities. -/
theorem short_zeta_separated_representatives :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 9/13 ≤ σ → 2 ≤ T →
      ∃ R : Finset ℂ, R ⊆ zetaZeroFinset σ T (2*T) ∧
        (R.image Complex.im).card = R.card ∧ oneSeparated (R.image Complex.im) ∧
        (zetaSlabCount σ T (2*T) : ℝ) ≤ C*Real.log (2*T)*(R.card : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := short_zeta_local_multiplicity_bound
  refine ⟨2*C, by positivity, ?_⟩
  intro σ T hσ hT
  have hB : 0 ≤ C*Real.log (2*T) := mul_nonneg hC.le
    (Real.log_nonneg (by linarith))
  obtain ⟨R, hR, hcard, hsep, hcount⟩ :=
    zetaSlab_separated_representatives σ T (2*T) hB (hlocal σ T hσ hT)
  pm_505 R hR hcard hsep
  calc
    _ ≤ 2*(C*Real.log (2*T))*(R.card : ℝ) := hcount
    _ = _ := by ring

end GuthMaynard.Improvement
