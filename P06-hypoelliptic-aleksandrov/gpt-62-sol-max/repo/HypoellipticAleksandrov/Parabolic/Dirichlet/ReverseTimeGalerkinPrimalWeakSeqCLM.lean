module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactnessCLM
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Continuous-functional weak subsequence of reverse-time Galerkin primal curves

This module extracts a subsequence of the canonical Bochner-valued reverse-time
Galerkin primal curves that converges under every continuous real linear functional.
It makes no strong convergence, equation-passage, trace, or weak-solution assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- The finite Galerkin solutions along `φ` converge to `U` under continuous linear tests. -/
def ReverseTimeGalerkinProblem.WeakLimit (initial : PDE.ScalarLp Ω 2)
    (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (φ : ℕ → ℕ) : Prop :=
  ∀ ell : ReverseTimeL2V P.hΩ (r₁ - r₀) →L[ℝ] ℝ,
    Tendsto (fun n => ell (reverseTimeGalerkinPrimal P (φ n) initial)) atTop (𝓝 (ell U))

/-- The canonical reverse-time Galerkin primal curves possess a strictly monotone
subsequence converging under every continuous real linear functional. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (φ : ℕ → ℕ), StrictMono φ ∧
      P.WeakLimit initial U φ := by
  letI : TopologicalSpace.SeparableSpace (H10HilbertGraph P.hΩ) :=
    instSeparableSpaceH10HilbertGraph P.hΩ
  letI : MeasureTheory.SFinite (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  letI : MeasurableSpace.CountablyGenerated ℝ := by infer_instance
  letI : MeasureTheory.IsSeparable (reverseTimeVolume (r₁ - r₀)) := by infer_instance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (ReverseTimeL2V P.hΩ (r₁ - r₀)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : TopologicalSpace.SeparableSpace (ReverseTimeL2V P.hΩ (r₁ - r₀)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le
    (fun N => reverseTimeGalerkinPrimal P N initial)
    (reverseTimeGalerkinPrimalRadius P initial)
    (fun N => norm_reverseTimeGalerkinPrimal_le_radius
      P initial N)

end HypoellipticAleksandrov.Parabolic.Dirichlet
