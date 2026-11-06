module

public import OAI.NumberTheory.DirichletL.Descent.ActiveCusp

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical
open CompletedGauss CubicEisenstein
noncomputable section
noncomputable local instance mixedQuotientFintype (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] :
    Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι]

def unmarkedSexticTwist (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) : ActualEisensteinCubic.O →* ℂ where
  toFun n := ∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

def mixedPrimeFunction (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (i : ι) (x : ActualEisensteinCubic.O ⧸ Ideal.span {p i}) : ℂ :=
  if i ∈ S then zeroMark x else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) x

theorem unmarkedSexticTwist_norm (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : ActualEisensteinCubic.O) :
    ‖unmarkedSexticTwist p hg j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one₀ (by simp)
    (fun i hi => FiniteRayExpansion.norm_char_le_one _ _)

theorem unmarkedSexticTwist_periodic (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i, p i}) (unmarkedSexticTwist p hg j S) := by
  intro x y hxy
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (Ideal.span {p i}) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hxy)
  simp_all

theorem mixedPrimeFunction_product (p : ι → ActualEisensteinCubic.O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : ActualEisensteinCubic.O) :
    (∏ i, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      unmarkedSexticTwist p hg j S n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if p i ∣ n then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, zeroMark,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

omit [Fintype ι] in
theorem markedThetaQuotient_mk (p : ι → ActualEisensteinCubic.O) (S : Finset ι)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (Q : Ideal ActualEisensteinCubic.O) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : ActualEisensteinCubic.O) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (n : ActualEisensteinCubic.O) :
    markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n) =
      fixedThetaTwist Ψ n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  unfold markedThetaQuotient
  have hcbase : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q :=
    hcQ.trans (Ideal.mul_mono_right Ideal.mul_le_left)
  rw [fixedThetaQuotient_mk Ψ Q hΨ c hcbase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hxy : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n ∈ Ideal.span {c} :=
    Ideal.Quotient.eq.mp (by simp)
  have hp : p i ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n :=
    (Finset.dvd_prod_of_mem p hi).trans (Ideal.mem_span_singleton.mp
      (Ideal.mul_le_right (Ideal.mul_le_right (hcQ hxy))))
  simp only [dvd_iff_dvd_of_dvd_sub hp]

end
end SevenEighths.InverseMoment

end OAI
