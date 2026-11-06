module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact

/-! # A uniform canonical spectral solver on the cutoff parameter compact set -/

@[expose] public section


open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Joint finite bounds for the canonical spectral weights imply matrix bounds. -/
theorem spectralTraceMatrix_uniform_bounds {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus lower upper : ℝ)
    (hlo : lower ≤ (b + cminus * negativeSpectralMass M) / positiveSpectralMass M)
    (hhi : (b + cminus * negativeSpectralMass M) / positiveSpectralMass M ≤ upper) :
    min 1 (min lower cminus) • (1 : PDE.Mat d) ≤ spectralTraceMatrix M b cminus ∧
      spectralTraceMatrix M b cminus ≤ max 1 (max upper cminus) • (1 : PDE.Mat d) := by
  rw [spectralTraceMatrix_eq_cfc M hM]
  have hcont : ContinuousOn (weightedSpectralSelector
      ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus)
      (spectrum ℝ M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  constructor
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply algebraMap_le_cfc _ _ M (ha := hM.isSelfAdjoint) (hf := hcont)
    intro t _
    unfold weightedSpectralSelector
    grind
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply cfc_le_algebraMap _ _ M (ha := hM.isSelfAdjoint) (hf := hcont)
    intro t _
    unfold weightedSpectralSelector
    grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
