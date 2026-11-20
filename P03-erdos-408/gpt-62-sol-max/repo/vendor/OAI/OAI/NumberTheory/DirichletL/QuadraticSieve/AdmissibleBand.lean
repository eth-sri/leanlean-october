module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound

@[expose] public section

namespace OAI

open ActualEisensteinCubic

/-- A family of admissible ideals whose norms all lie in the given interval. -/
abbrev IdealFamilyBand {ι : Type*} (valid : Ideal O → Prop) (I : ι → Ideal O) (lo hi : ℝ) : Prop :=
  ∀ i, valid (I i) ∧ lo ≤ (Ideal.absNorm (I i) : ℝ) ∧ (Ideal.absNorm (I i) : ℝ) ≤ hi

/-- A family of admissible ideals with a common upper bound on their norms. -/
abbrev IdealFamilyUpTo {ι : Type*} (valid : Ideal O → Prop) (I : ι → Ideal O) (hi : ℝ) : Prop :=
  ∀ i, valid (I i) ∧ (Ideal.absNorm (I i) : ℝ) ≤ hi

end OAI
