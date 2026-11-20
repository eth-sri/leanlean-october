module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.GaussianLattice

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open AbelianQuotient.Theta

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] (z : E) {a : ℝ} (ha : 0 < a)

include ha in
theorem summable_shiftedGaussian :
    Summable (fun ℓ : L => Real.exp (-a * ‖z + (ℓ : E)‖ ^ 2)) := by
  apply (((summable_latticeGaussian L (half_pos ha)).norm).mul_left _).of_norm_bounded
  intro ℓ
  have h := norm_latticeGaussian_add_le ha.le z (ℓ : E)
  rw [norm_latticeGaussian] at h
  simpa [norm_latticeGaussian] using h

include ha in
theorem summable_shiftedGaussian_punctured :
    Summable (fun ℓ : {ℓ : L // z + (ℓ : E) ≠ 0} =>
      Real.exp (-a * ‖z + ((ℓ : L) : E)‖ ^ 2)) := (summable_shiftedGaussian L z ha).comp_injective Subtype.val_injective

end DedekindZetaZeroFree

end
