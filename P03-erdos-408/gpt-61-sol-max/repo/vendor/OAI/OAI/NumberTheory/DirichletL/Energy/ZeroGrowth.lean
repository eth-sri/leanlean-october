module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands QuadraticInitialBound


def ZeroGrowthAt (Q : Ideal HeckeFamily.O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)  :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ,
    0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.plainEnergy p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree *
        Z ^ (max s.width (length Z X₁ + length Z X₂) + ε)

lemma zeroGrowth_of_zeroAt  Q   a b bΦ Bmask L M ε Z 
     degree   S   C  (hC : 0 ≤ C)
    (h : ZeroAt Q a b bΦ Bmask L M ε Z degree S C) :
    ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  apply (h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
  have he : s.width + ε ≤ max s.width (length Z X₁ + length Z X₂) + ε := by
    simp_all
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one he)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _)

end SevenEighths.CenteredMomentEnergyZeroGrowth

end

end OAI
