module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCells

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

def physicalScales (X : ℝ) (k : SourceIndex) (l : ℕ)  :=
  rawScales k l (X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma physicalScales_pos  X  (hX : 0<X)  k   l  :
    ∀i,0<physicalScales X k l i := by
  apply rawScales_pos
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma physicalScales_products  X   k   l  :
    physicalScales X k l 0*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 7=X ∧
    physicalScales X k l 1*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 8=X := ⟨mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos (k 0)) (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos (k 2))) (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos l))), mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos (k 1)) (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos (k 2))) (OAI.SevenEighths.InverseSecondSourceBlocks.dyadScale_pos l)))⟩

theorem physicalScales_rpow  Z r  (hZ : 1<Z)  k   l  :
    physicalScales (Z^r) k l=fun i=>Z^(![Real.logb Z (dyadScale (k 0)),
      Real.logb Z (dyadScale (k 1)),Real.logb Z (dyadScale (k 2)),
      Real.logb Z (dyadScale (k 3)),Real.logb Z (dyadScale (k 4)),Real.logb Z (dyadScale l),
      Real.logb Z (dyadScale (k 5)),
      r-Real.logb Z (dyadScale (k 0))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l),
      r-Real.logb Z (dyadScale (k 1))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l)] i) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he (n : ℕ) : Z^(Real.logb Z (dyadScale n))=dyadScale n :=
    Real.rpow_logb hz (ne_of_gt hZ) (dyadScale_pos n)
  funext i
  fin_cases i <;> simp [physicalScales,rawScales,he,Real.rpow_sub hz,div_div]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
