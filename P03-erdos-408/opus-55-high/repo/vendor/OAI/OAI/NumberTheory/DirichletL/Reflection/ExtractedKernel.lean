module

public import OAI.NumberTheory.DirichletL.Reflection.Extraction

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section

def extractedRowFactor (D1 D2 K : Ideal ActualEisensteinCubic.O) : ℂ := quadraticRow K (primaryGenerator (D1*D2))
def extractedSlotFactor (D1 D2 P : Ideal ActualEisensteinCubic.O) : ℂ :=
  inverseCubicKernel P D1 * (if IsCoprime P D2 then 1 else 0)

lemma extractedRowFactor_norm_le_one (D1 D2 K : Ideal ActualEisensteinCubic.O) : ‖extractedRowFactor D1 D2 K‖ ≤ 1 :=
  quadraticRow_norm_le_one K _

lemma extractedSlotFactor_norm_le_one (D1 D2 P : Ideal ActualEisensteinCubic.O) : ‖extractedSlotFactor D1 D2 P‖ ≤ 1 := by
  unfold extractedSlotFactor
  split_ifs
  · simpa using inverseCubicKernel_norm_le_one P D1
  simp

lemma coprime_product_mask (P D b : Ideal ActualEisensteinCubic.O) :
    (if IsCoprime P (D*b) then (1:ℂ) else 0) =
      (if IsCoprime P D then 1 else 0)*(if IsCoprime P b then 1 else 0) := by
  by_cases hD : IsCoprime P D <;> by_cases hb : IsCoprime P b
  · simp [hD,hb,hD.mul_right hb]
  · have hn : ¬IsCoprime P (D*b) := fun h => hb (h.of_isCoprime_of_dvd_right (by simp))
    simp_all
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (by simp))
    simp_all
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (by simp))
    simp_all

theorem forced_dual_kernel_factor (D1 D2 K P n b : Ideal ActualEisensteinCubic.O)
    (hK : Admissible K) (hP : primaryGenerator P ≠ 0) :
    quadraticRow K (primaryGenerator ((D1*n)*(D2*b)))*inverseCubicKernel P (D1*n)*
      (if IsCoprime P (D2*b) then 1 else 0)*(if IsCoprime K P then 1 else 0) =
      (extractedRowFactor D1 D2 K*extractedSlotFactor D1 D2 P)*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
        (if IsCoprime P b then 1 else 0)*(if IsCoprime K P then 1 else 0) := by
  rw [show (D1*n)*(D2*b)=(D1*D2)*(n*b) by ring,primaryGenerator_mul,
    canonical_quadraticRow_argument_mul K hK,inverseCubicKernel_mul_right P D1 n hP,
    coprime_product_mask]
  unfold extractedRowFactor extractedSlotFactor
  ring

def extractedFrozenColumn {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (n b : Ideal ActualEisensteinCubic.O) : ℂ :=
  normalizedFrozenColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)

lemma extractedFrozenColumn_norm_le_one {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal ActualEisensteinCubic.O) : ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
  normalizedFrozenColumn_norm_le_one F jF e A hA _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
