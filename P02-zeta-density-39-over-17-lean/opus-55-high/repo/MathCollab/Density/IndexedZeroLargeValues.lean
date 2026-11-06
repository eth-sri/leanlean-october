module
public import MathCollab.Density.ZeroSeparation
public import MathCollab.Density.LargeValues
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Arbitrary finite-index version of the proved conditional bridge from a finite family detecting every actual zero and a
local multiplicity bound to the proved large-values estimate. The constant
precedes the slab, ambient height, bin bound, and entire polynomial family.
No detector or local zero-count estimate is asserted by this theorem. -/
theorem zetaSlab_large_values_cover_indexed {ι : Type*} {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lo hi H B : ℝ) (J : Finset ι)
      (N : ι → ℕ) (V : ι → ℝ) (coeff : ι → ℕ → ℂ),
      2 ≤ H → 0 ≤ B → hi ≤ lo+H →
      (∀ k : ℤ, (∑ ρ ∈ (zetaZeroFinset σ lo hi).filter
        (fun ρ => ordinateBin ρ = k), (zetaMultiplicity ρ : ℝ)) ≤ B) →
      (∀ j ∈ J, 0 < N j ∧ 0 < V j ∧ H^(1/3 : ℝ) ≤ (N j : ℝ) ∧
        (N j : ℝ) ≤ H ∧ (N j : ℝ)^(3/4+κ) ≤ V j ∧
        ∀ n ∈ Finset.Ioc (N j) (2*N j), ‖coeff j n‖ ≤ 1) →
      (∀ ρ ∈ zetaZeroFinset σ lo hi, ∃ j ∈ J,
        V j ≤ ‖detectingPolynomial (N j) (coeff j) ρ.im‖) →
      (zetaSlabCount σ lo hi : ℝ) ≤ C*B*H^ε*
        ∑ j ∈ J, ((N j : ℝ)^2/(V j)^2+(N j : ℝ)^3*Real.sqrt H/(V j)^4) := by
  classical
  pm_98 C hC hLV large_values hκ hε
  refine ⟨2*C, by positivity, ?_⟩
  intro σ lo hi H B J N V coeff hH hB hhi hlocal hadm hcover
  obtain ⟨R, hR, hcard, hsep, hcount⟩ := zetaSlab_separated_representatives σ lo hi hB hlocal
  pm_4292
  have hWj : ∀ j ∈ J, ((Wj j).card : ℝ) ≤ C*H^ε*F j := by
    pm_4293
    · refine ⟨lo, ?_⟩
      pm_6294
      have hz := mem_zetaZeroFinset.mp (hR hρ)
      exact ⟨hz.2.2.1, hz.2.2.2.trans hhi⟩
    pm_4294
  pm_4291

end MathCollab.Density
