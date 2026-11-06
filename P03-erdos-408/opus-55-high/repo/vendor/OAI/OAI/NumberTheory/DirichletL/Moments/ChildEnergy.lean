module

public import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
public import OAI.NumberTheory.DirichletL.Moments.Cauchy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth

theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : ActualEisensteinCubic.O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  grind

theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : ActualEisensteinCubic.O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  grind

end SevenEighths.CenteredMomentChildEnergy

end

end OAI
