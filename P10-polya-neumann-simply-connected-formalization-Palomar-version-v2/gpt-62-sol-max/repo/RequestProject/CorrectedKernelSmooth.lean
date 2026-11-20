module

public import RequestProject.CorrectedKernel
public import RequestProject.SmallTransport

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

/-- The transport is differentiable on `[0, L]` with `W' = C_E W` when `γ'` is continuous
there. -/
lemma hasDerivWithinAt_transport
    (hγ' : ContinuousOn (deriv γ) (Set.Icc 0 (2 * π))) (hW : IsTransport γ E W) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasDerivWithinAt W (transportCoeff γ E θ * W θ) (Set.Icc 0 (2 * π)) θ := by
  have hco : Continuous (coeffOf E) := by
    unfold coeffOf
    fun_prop
  have hC := hco.comp_continuousOn hγ'
  set F : ℝ → Ell2 →L[ℂ] Ell2 := fun s => transportCoeff γ E s * W s with hFdef
  have hF := hC.mul hW.1
  have hsub : Set.uIcc 0 θ ⊆ Set.Icc 0 (2 * π) := by
    rw [Set.uIcc_of_le hθ.1]; exact Set.Icc_subset_Icc le_rfl hθ.2
  haveI : Fact (θ ∈ Set.Icc 0 (2 * π)) := ⟨hθ⟩
  haveI : SecondCountableTopologyEither ℝ (Ell2 →L[ℂ] Ell2) :=
    secondCountableTopologyEither_of_left _ _
  have hint : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, F s) (F θ) (Set.Icc 0 (2 * π)) θ :=
    intervalIntegral.integral_hasDerivWithinAt_right ((hF.mono hsub).intervalIntegrable)
      (hF.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc θ) (hF θ hθ)
  exact (hint.const_add 1).congr_of_mem (fun u hu => hW.2 u hu) hθ

end PolyaNeumann
