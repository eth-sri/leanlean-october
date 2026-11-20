module
/- Adapted from audited Density.LocalZeroCount at eff263d7, whose Jensen
 proof derives from Scott McColm (MIT). The same actual zero count and
 multiplicities are retained; a radius3/2 disk also covers Re(rho)>=3/5. -/
public import MathCollab.Density.LocalZeroCount

@[expose] public section
open Complex Filter Set MeasureTheory MathCollab.Density
open scoped Topology BigOperators
open MathCollab.Density.ZetaGrowth
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

/-- Unconditional logarithmic restoration of all analytic multiplicities. -/
theorem short_zeta_separated_representatives :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 9/13 ≤ σ → 2 ≤ T →
      ∃ R : Finset ℂ, R ⊆ zetaZeroFinset σ T (2*T) ∧
        (R.image Complex.im).card = R.card ∧ oneSeparated (R.image Complex.im) ∧
        (zetaSlabCount σ T (2*T) : ℝ) ≤ C*Real.log (2*T)*(R.card : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := zeta_local_multiplicity_bound_from_three_fifths
  refine ⟨2*C, by positivity, ?_⟩
  intro σ T hσ hT
  have hB : 0 ≤ C*Real.log (2*T) := mul_nonneg hC.le
    (Real.log_nonneg (by linarith))
  obtain ⟨R, hR, hcard, hsep, hcount⟩ :=
    zetaSlab_separated_representatives σ T (2*T) hB (hlocal σ T (by linarith) hT)
  refine ⟨R, hR, hcard, hsep, ?_⟩
  calc
    _ ≤ 2*(C*Real.log (2*T))*(R.card : ℝ) := hcount
    _ = _ := by ring

end GuthMaynard.Improvement
