module

public import OAI.NumberTheory.DirichletL.CubicSieve.SquarefreeTransfer
public import OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def rowPowerfulPart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P)).prod

def rowSimplePart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P)).prod

theorem rowPowerfulPart_ne_zero (I : Ideal O) : rowPowerfulPart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowSimplePart_ne_zero (I : Ideal O) : rowSimplePart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_rowPowerfulPart (I : Ideal O) :
    normalizedFactors (rowPowerfulPart I)=
      (normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_rowSimplePart (I : Ideal O) :
    normalizedFactors (rowSimplePart I)=
      (normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem rowPowerfulPart_powerful (I : Ideal O) : PowerfulIdeal (rowPowerfulPart I) := by
  refine ⟨rowPowerfulPart_ne_zero I,?_⟩
  intro P hP
  rw [normalizedFactors_rowPowerfulPart] at hP ⊢
  have hp := (Multiset.mem_filter.mp hP).2
  rw [Multiset.count_filter,ite_eq_left hp]
  exact hp

theorem rowSimplePart_squarefree (I : Ideal O) : Squarefree (rowSimplePart I) := by
  apply (squarefree_iff_nodup_normalizedFactors (rowSimplePart_ne_zero I)).mpr
  rw [normalizedFactors_rowSimplePart]
  apply Multiset.nodup_iff_count_le_one.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs <;> omega

theorem row_powerful_simple_product (I : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowSimplePart I=I := by
  rw [rowPowerfulPart,rowSimplePart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

end

open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid

def squarefreeMaskPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P∣R)).prod

def squarefreeResidualPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬P∣R)).prod

theorem squarefreeMaskPart_ne_zero (I R : Ideal O) : squarefreeMaskPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem squarefreeResidualPart_ne_zero (I R : Ideal O) : squarefreeResidualPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_squarefreeMaskPart (I R : Ideal O) :
    normalizedFactors (squarefreeMaskPart I R)=(normalizedFactors I).filter (fun P => P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_squarefreeResidualPart (I R : Ideal O) :
    normalizedFactors (squarefreeResidualPart I R)=(normalizedFactors I).filter (fun P => ¬P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem squarefreeResidualPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeResidualPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeResidualPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeResidualPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefree_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    squarefreeMaskPart I R*squarefreeResidualPart I R=I := by
  rw [squarefreeMaskPart,squarefreeResidualPart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem squarefreeResidualPart_coprime (I R : Ideal O) : IsCoprime (squarefreeResidualPart I R) R := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (squarefreeResidualPart_ne_zero I R)).mpr
  intro P hp hr hP
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero I R)).mpr ⟨hP,hp⟩
  rw [normalizedFactors_squarefreeResidualPart] at hm
  exact (Multiset.mem_filter.mp hm).2 hr

theorem squarefreeMaskPart_dvd (I R : Ideal O) (hI : Squarefree I) : squarefreeMaskPart I R∣R := by
  by_cases hR : R=0
  · rw [hR]; exact dvd_zero _
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarefreeMaskPart_ne_zero I R) hR).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  apply Multiset.le_iff_count.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs with hp
  · have hn := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI) P
    by_cases hz : (normalizedFactors I).count P=0
    · omega
    · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hz)
      have hr := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hR).mpr ⟨prime_of_normalized_factor P hm,hp⟩
      have hc := Multiset.count_pos.mpr hr
      omega
  · omega

def rowMaskPart (I R : Ideal O) : Ideal O := squarefreeMaskPart (rowSimplePart I) R
def rowResidualPart (I R : Ideal O) : Ideal O := squarefreeResidualPart (rowSimplePart I) R

theorem row_powerful_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowMaskPart I R*rowResidualPart I R=I := by
  rw [mul_assoc,rowMaskPart,rowResidualPart,squarefree_mask_residual_product _ _ (rowSimplePart_ne_zero I),
    row_powerful_simple_product I hI]

theorem rowMaskPart_dvd (I R : Ideal O) : rowMaskPart I R∣R :=
  squarefreeMaskPart_dvd _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_squarefree (I R : Ideal O) : Squarefree (rowResidualPart I R) :=
  squarefreeResidualPart_squarefree _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_admissible (I R : Ideal O) (hbad : ∀P∈fixedBadPrimes,P∣R) :
    Admissible (rowResidualPart I R) :=
  admissible_of_squarefree_coprime_bad _ R (rowResidualPart_squarefree I R)
    (squarefreeResidualPart_coprime (rowSimplePart I) R) hbad

theorem rowResidualPart_prime_exponent (I R P : Ideal O)
    (hP : P∈normalizedFactors (rowResidualPart I R)) :
    P∈normalizedFactors I ∧ (normalizedFactors I).count P=1 ∧ ¬P∣R := by
  rw [rowResidualPart,normalizedFactors_squarefreeResidualPart] at hP
  obtain ⟨hs,hr⟩ := Multiset.mem_filter.mp hP
  rw [normalizedFactors_rowSimplePart] at hs
  obtain ⟨hi,hcount⟩ := Multiset.mem_filter.mp hs
  exact ⟨hi,by have hp := Multiset.count_pos.mpr hi; omega,hr⟩

theorem rowResidualPart_norm (I R : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowResidualPart I R):ℝ)=(Ideal.absNorm I:ℝ)/
      ((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I R):ℝ)) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm (rowMaskPart I R):ℝ)≠0 := by
    exact_mod_cast (fun hz => squarefreeMaskPart_ne_zero (rowSimplePart I) R (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff (mul_ne_zero hp ht)).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_mask_residual_product I R hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he

end CompletedGauss

namespace SecondPassArithmetic

section

open MeasureTheory
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff gCoeff)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

section
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end

open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

end SecondPassArithmetic

end

end OAI
