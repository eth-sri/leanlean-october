module
public import OAI.NumberTheory.DirichletL.Moments.RowNorm
public import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm ConcreteTraceCRT
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

theorem rowEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖rowPolynomial S a c z‖^2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖^2/K)) := by pm_2878 row_pair_summable rowPolynomial_norm_sq

end SevenEighths.CenteredMomentPlainEnergy

end

end OAI
