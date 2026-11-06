module

public import OAI.NumberTheory.DirichletL.Moments.PlainEnergy
public import OAI.NumberTheory.DirichletL.Moments.Cauchy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentPlainChildEnergy
open CanonicalRowCompletion CenteredMomentRowNorm CenteredMomentCauchy
open CenteredMomentSmooth

theorem leftColumn_eq_rowPolynomial {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : ActualEisensteinCubic.O) (t : ℝ) :
    leftColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      rowPolynomial S a (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn rowPolynomial
  grind

theorem rightColumn_eq_star_rowPolynomial {α : Type*} (S : Finset α) (a : α → ActualEisensteinCubic.O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : ActualEisensteinCubic.O) (t : ℝ) :
    rightColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      star (rowPolynomial S a (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, rowPolynomial, star_sum, star_mul, star_star]
  grind

end SevenEighths.CenteredMomentPlainChildEnergy

end

end OAI
