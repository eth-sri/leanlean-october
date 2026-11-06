module

public import OAI.NumberTheory.DirichletL.Reflection.Shape
public import OAI.NumberTheory.DirichletL.CubicSieve.Ideal

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section

@[simp] lemma shapeArgument_one : shapeArgument (1:ActualEisensteinCubic.O)=1 := by
  simp [shapeArgument]

lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) ActualEisensteinCubic.O}
    (s : FixedCuspShape H) (c r : ActualEisensteinCubic.O) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa using stratumShapeFactor_mul s c r 1

lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)

lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) ActualEisensteinCubic.O} (s : FixedCuspShape H) (c : ActualEisensteinCubic.O) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]

lemma row_shape_weight_norm (r : Ideal ActualEisensteinCubic.O→ℂ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryGenerator K)‖=‖r K‖ := by
  have hk := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]

lemma slot_shape_weight_norm (aw : Ideal ActualEisensteinCubic.O→ℂ) (P : Ideal ActualEisensteinCubic.O) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]
end
end SevenEighths.InverseReflectedPhase

end OAI
