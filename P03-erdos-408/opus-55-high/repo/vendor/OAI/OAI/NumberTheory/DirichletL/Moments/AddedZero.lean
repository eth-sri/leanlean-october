module

public import OAI.NumberTheory.DirichletL.Moments.ZeroMode
public import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
public import OAI.NumberTheory.DirichletL.Moments.Tail
public import OAI.NumberTheory.DirichletL.Moments.Extraction

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve
open CenteredMomentRectangle
open UniqueFactorizationMonoid

lemma supported_one_ideal : Supported (1 : Ideal ActualEisensteinCubic.O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : ActualEisensteinCubic.O)}) := by
  simpa using supported_one_ideal

def tupleProduct {r : ℕ} (v : Fin r → Ideal ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O := ∏ i, v i

def originalCoefficient (N : ℕ) (c : ActualEisensteinCubic.O) (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal ActualEisensteinCubic.O) (t : ℝ) (ν : Fin N → Ideal ActualEisensteinCubic.O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal ActualEisensteinCubic.O) (v : Fin (N + 2) → Ideal ActualEisensteinCubic.O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

end SevenEighths.CenteredMomentAddedZero

end

end OAI
