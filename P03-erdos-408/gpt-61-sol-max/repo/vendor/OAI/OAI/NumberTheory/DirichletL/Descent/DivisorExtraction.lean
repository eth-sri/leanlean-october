module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.Quotients

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum



theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal ActualEisensteinCubic.O)
    (hP : primaryGenerator P ≠ 0) (hcm : primaryGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := OAI.SevenEighths.InverseMoment.inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm fun hcop => hRr (IsCoprime.of_isCoprime_of_dvd_right (IsCoprime.of_isCoprime_of_dvd_left (IsCoprime.of_isCoprime_of_dvd_right hcop (dvd_mul_right c m)) hRP) hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal ActualEisensteinCubic.O)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal ActualEisensteinCubic.O) (hRr : IsCoprime R r) (F : Ideal ActualEisensteinCubic.O → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal ActualEisensteinCubic.O) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F


end SevenEighths.InverseMoment

end OAI
