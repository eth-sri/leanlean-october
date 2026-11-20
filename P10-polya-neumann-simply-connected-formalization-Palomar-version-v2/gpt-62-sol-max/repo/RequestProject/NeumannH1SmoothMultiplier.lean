module

public import RequestProject.TraceH1
public import RequestProject.NeumannH1Multiplier

/-!
# Multiplication in the actual weak-gradient H¹ space

A globally smooth coefficient with bounded value and first derivatives defines
a genuine bounded H¹ multiplication operator. The product rule is proved by
testing the original weak gradient against the compact product aφ. Smooth
compact coefficients supply the bounds, so this applies to actual cutoff
coordinate functions without an assumed weak product rule.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Topology

/-- A coefficient bounded on the whole plane. -/
abbrev SmoothH1Coefficient := H1Coefficient (Set.univ : Set ℂ)

/-- Smooth compact coefficients have actual global value and derivative bounds. -/
theorem smoothTraceTests_exists_h1Coefficient_bound (a : smoothTraceTests) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ z, ‖a z‖ ≤ B) ∧
      ∀ (i : Fin 2) z, ‖fderiv ℝ (a : ℂ → ℂ) z (coordDir i)‖ ≤ B := by
  obtain ⟨B, hB⟩ := a.property.2.1.exists_bound_of_continuous a.property.1.continuous
  obtain ⟨B₀, hB₀⟩ := (a.property.dirD (coordDir 0)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 0)).1.continuous
  obtain ⟨B₁, hB₁⟩ := (a.property.dirD (coordDir 1)).2.1.exists_bound_of_continuous
    (a.property.dirD (coordDir 1)).1.continuous
  refine ⟨max 0 (max B (max B₀ B₁)), le_max_left _ _, ?_, ?_⟩
  grind
  · intro i z
    fin_cases i
    aesop
    aesop

/-- An actual compact smooth function as a bounded H¹ coefficient. -/
def smoothTraceTestsH1Coefficient (a : smoothTraceTests) : SmoothH1Coefficient where
  toFun := a
  smooth := a.property.1
  bound := Classical.choose (smoothTraceTests_exists_h1Coefficient_bound a)
  bound_nonneg := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).1
  value_bound z _ := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.1 z
  derivative_bound i z _ := (Classical.choose_spec (smoothTraceTests_exists_h1Coefficient_bound a)).2.2 i z


section Restrict

variable (Ω : Set ℂ) (a : SmoothH1Coefficient)

local notation "aΩ" => a.restrict (Set.subset_univ Ω)

abbrev h1SmoothCoefficientL2 := h1CoefficientL2 Ω aΩ
abbrev h1SmoothCoefficientDerivativeL2 := h1CoefficientDerivativeL2 Ω aΩ
abbrev neumannH1SmoothMultiplier := neumannH1CoefficientMultiplier Ω aΩ

theorem h1SmoothCoefficientL2_ae (u : L2 Ω) :
    (h1SmoothCoefficientL2 Ω a u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => a z * u z :=
  h1CoefficientL2_ae Ω aΩ u

theorem h1SmoothCoefficientDerivativeL2_ae (i : Fin 2) (u : L2 Ω) :
    (h1SmoothCoefficientDerivativeL2 Ω a i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (a : ℂ → ℂ) z (coordDir i) * u z :=
  h1CoefficientDerivativeL2_ae Ω aΩ i u

theorem h1Gradient_neumannH1SmoothMultiplier (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothCoefficientL2 Ω a (h1Gradient Ω i u) +
      h1SmoothCoefficientDerivativeL2 Ω a i (h1Value Ω u) :=
  h1Gradient_neumannH1CoefficientMultiplier Ω aΩ u i

end Restrict

def smoothCoefficientTestProduct (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    smoothTraceTests :=
  ⟨fun z => a z * f z, coefficient_test_mul a f.property⟩


/-- The completed product agrees with the actual compact smooth product. -/
theorem neumannH1SmoothMultiplier_smooth {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (a : SmoothH1Coefficient) (f : smoothTraceTests) :
    neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f) =
      smoothTraceH1 Ω (smoothCoefficientTestProduct a f) := by
  apply h1Value_injective hΩ
  simp only [h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae Ω a (h1Value Ω (smoothTraceH1 Ω f)), (smoothTraceTests_memLp Ω f).coeFn_toLp, (smoothTraceTests_memLp Ω (smoothCoefficientTestProduct a f)).coeFn_toLp] with x; aesop

/-- Multiplication by the actual boundary values of the same coefficient. -/
def h1SmoothBoundaryMultiplier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  lpBoundedMultiplier (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ) (mem_univ _)))

theorem h1SmoothBoundaryMultiplier_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) (g : BoundaryL2) :
    (h1SmoothBoundaryMultiplier hγ a g : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))] fun θ => a (γ θ) * g θ :=
  lpBoundedMultiplier_ae (fun θ => a (γ θ))
    (a.smooth.continuous.comp hγ.lipschitz.choose_spec.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun θ => a.value_bound (γ θ) (mem_univ _))) g

/-- The physical trace product rule for every actual H¹ vector follows from
the dense smooth restrictions and the two already bounded product operators. -/
theorem h1BoundaryTrace_neumannH1SmoothMultiplier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (a : SmoothH1Coefficient) (u : NeumannH1 Ω) :
    h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a u) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a v) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ v)) u ?_ ?_
  · exact isClosed_eq ((h1BoundaryTrace hb hL hγ).continuous.comp
      (neumannH1SmoothMultiplier Ω a).continuous)
      ((h1SmoothBoundaryMultiplier hγ a).continuous.comp (h1BoundaryTrace hb hL hγ).continuous)
  · intro f
    change h1BoundaryTrace hb hL hγ (neumannH1SmoothMultiplier Ω a (smoothTraceH1 Ω f)) =
      h1SmoothBoundaryMultiplier hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f))
    rw [neumannH1SmoothMultiplier_smooth hL.1.1]
    apply Lp.ext
    filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ (smoothCoefficientTestProduct a f),
      h1SmoothBoundaryMultiplier_ae hγ a (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f)),
      h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hp hm hf
    rw [hp, hm, hf]
    rfl

end PolyaNeumann

end
