module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm

/-!
# Squared L2 energy under weak-derivative-family truncation
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory
open scoped BigOperators ENNReal

variable {d M L : ℕ}

private def castLEEmbedding  (hML : M ≤ L) :
    ParabolicDerivativeIndex d M ↪ ParabolicDerivativeIndex d L where
  toFun := ParabolicDerivativeIndex.castLE hML
  inj' := by
    intro beta gamma h
    apply Subtype.ext
    exact congrArg
      (fun delta : ParabolicDerivativeIndex d L ↦ delta.1) h

/-- Truncating the parabolic weight bound cannot increase the squared
finite-family `L²` norm. -/
theorem squaredL2Norm_truncate_le
     {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hML : M ≤ L) :
    squaredL2Norm (F.truncate hML) ≤ squaredL2Norm F := (id
  (Trans.trans
    (Trans.trans
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              ∑ beta, (eLpNorm ((F.truncate hML).representative beta) 2 (timeVelocityVolumeOn U)).toReal ^ 2 = _a)
            (Finset.sum_map Finset.univ (castLEEmbedding hML) fun beta =>
              (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U)).toReal ^ 2)))
        (Eq.refl (∑ beta, (eLpNorm ((F.truncate hML).representative beta) 2 (timeVelocityVolumeOn U)).toReal ^ 2)))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (Finset.map (castLEEmbedding hML) Finset.univ))
        fun beta a a_1 => sq_nonneg (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U)).toReal))
    rfl))

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
