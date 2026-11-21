module

public import DedekindZetaZeroFree.Moments.Principal.TripleMellin.TermEvaluation

@[expose] public section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

export TripleMellinRaw (poissonLocalEquiv poissonAdditiveMeasure MellinNormalizationData
  principalMellinWeights principalMellinFrequencySum principalTripleMellinKernel
  principalTripleMellinHeights tripleMellinNormalization principalTripleMellinIntegral
  iteratedTripleMellinIntegral)

section

variable (A : SArithmeticData F) (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
  (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A σ η hS)
include A σ η hS P

def ExactTripleMellin : Prop :=
  ∀ X Y Z : {x : ℝ // 0 < x},
    Integrable (principalTripleMellinHeights A σ η hS P X.val Y.val Z.val) ∧
    principalProbe A σ η hS P X Y Z =
      principalTripleMellinIntegral A σ η hS P X.val Y.val Z.val ∧
    ∀ order : Equiv.Perm (Fin 3),
      principalProbe A σ η hS P X Y Z =
        iteratedTripleMellinIntegral
          (principalTripleMellinHeights A σ η hS P X.val Y.val Z.val) order

theorem probe_exact_triple_mellin (N : MellinNormalizationData A σ η hS P) :
    ExactTripleMellin A σ η hS P := by
  intro X Y Z
  have he : principalProbe A σ η hS P X Y Z =
      principalTripleMellinIntegral A σ η hS P X.val Y.val Z.val :=
    TripleMellin.probe_eq_mellin_integral P N X Y Z
  refine ⟨TripleMellin.heights_integrable P X.val Y.val Z.val
    X.property Y.property Z.property, he, ?_⟩
  intro order
  exact he.trans (TripleMellin.integral_eq_every_order P X.val Y.val Z.val
    X.property Y.property Z.property order)

theorem ExactTripleMellin.initial_order (h : ExactTripleMellin A σ η hS P)
    (X Y Z : {x : ℝ // 0 < x}) :
    principalProbe A σ η hS P X Y Z =
      tripleMellinNormalization * ∫ τξ : ℝ, ∫ τw : ℝ, ∫ τz : ℝ,
        principalTripleMellinKernel A σ η hS P X.val Y.val Z.val
          (4 + (τξ : ℂ) * Complex.I) (4 + (τw : ℂ) * Complex.I)
          (2 + (τz : ℂ) * Complex.I) := by
  simpa [iteratedTripleMellinIntegral, principalTripleMellinHeights] using
    (h X Y Z).2.2 (Equiv.refl (Fin 3))

end

end
end NormalizedProbe
end DedekindZetaZeroFree
