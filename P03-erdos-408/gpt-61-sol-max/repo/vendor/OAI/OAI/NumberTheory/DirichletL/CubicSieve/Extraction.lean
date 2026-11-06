module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.Norm

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge



theorem extracted_norm_product (I : Ideal ActualEisensteinCubic.O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono  {M N M' N'}  (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := OAI.SevenEighths.CubicSieve.family_squared_norm_le Subtype.val Subtype.val Subtype.val_injective Subtype.val_injective M' N' (fun I => ⟨(OAI.SevenEighths.CubicSieve.mem_idealRange.mp I.property).left, LE.le.trans (OAI.SevenEighths.CubicSieve.mem_idealRange.mp I.property).right hM⟩) fun J => ⟨(OAI.SevenEighths.CubicSieve.mem_idealRange.mp J.property).left, LE.le.trans (OAI.SevenEighths.CubicSieve.mem_idealRange.mp J.property).right hN⟩


end SevenEighths.CubicSieve

end OAI
