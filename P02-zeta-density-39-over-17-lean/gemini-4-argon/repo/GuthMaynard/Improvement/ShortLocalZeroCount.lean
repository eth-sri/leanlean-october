module
public import MathCollab.Density.LocalZeroCount

@[expose] public section
open Complex Filter Set MeasureTheory MathCollab.Density
open scoped Topology BigOperators
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

alias short_zeta_unit_bin_sum_le_jensen := MathCollab.Density.zeta_unit_bin_sum_le_jensen
alias short_zeta_local_multiplicity_bound := MathCollab.Density.zeta_local_multiplicity_bound

theorem short_zeta_separated_representatives :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 9/13 ≤ σ → 2 ≤ T →
      ∃ R ⊆ zetaZeroFinset σ T (2*T),
        (R.image Complex.im).card = R.card ∧
        oneSeparated (R.image Complex.im) ∧
        (zetaSlabCount σ T (2*T) : ℝ) ≤ C * Real.log (2*T) * R.card := by
  obtain ⟨C, hC, hlocal⟩ := short_zeta_local_multiplicity_bound
  refine ⟨2*C, by positivity, fun σ T hσ hT => ?_⟩
  have hB : 0 ≤ C * Real.log (2*T) := mul_nonneg hC.le (Real.log_nonneg (by linarith))
  obtain ⟨R, hR, hcard, hsep, hcount⟩ :=
    zetaSlab_separated_representatives σ T (2*T) hB (hlocal σ T (by linarith) hT)
  exact ⟨R, hR, hcard, hsep, hcount.trans_eq (by ring)⟩

