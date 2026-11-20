module

public import ALCS.ContinuityLinfty

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [xComplete : CompleteSpace X]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [uComplete : CompleteSpace U]

local notation "μ₊" => volume.restrict (Ici (0 : ℝ))
local notation:max "L∞⁺" U:max => Lp U ∞ μ₊

variable (T : ℝ → X →L[𝕜] X) (Φ : ℝ → L∞⁺ U →L[𝕜] X)
  (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
  (hT_semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
  (hT_cont : ∀ x : X, Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x))
  (hΦ_concat : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → ∀ u v w : L∞⁺ U,
    (⇑w =ᵐ[μ₊] fun s => if s < τ then u s else v (s - τ)) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v)

-- Retain the benchmark's completeness hypotheses in the public signatures.
set_option linter.unusedSectionVars false
include xComplete uComplete hT_zero hT_semigroup hT_cont hΦ_concat

/-- **Theorem 1.5** (zero-class property). -/
theorem zero_class : Tendsto (fun t => ‖Φ t‖) (𝓝[≥] 0) (𝓝 0) :=
  (ALCS.mk ⟨T, hT_zero, hT_semigroup, hT_cont⟩ Φ hΦ_concat).zero_class

/-- **Corollary 1.6** (continuity of the solution). -/
theorem continuousOn_Phi (u : L∞⁺ U) : ContinuousOn (fun t => Φ t u) (Ici 0) :=
  (ALCS.mk ⟨T, hT_zero, hT_semigroup, hT_cont⟩ Φ hΦ_concat).continuousOn_Phi u

end PalomarALCS
