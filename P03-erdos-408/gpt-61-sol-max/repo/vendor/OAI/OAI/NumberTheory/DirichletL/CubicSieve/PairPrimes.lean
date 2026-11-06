module

public import OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section


def pairPrime (I J ) : PrimeIndex I ⊕ PrimeIndex J → Ideal ActualEisensteinCubic.O :=
  Sum.elim Subtype.val Subtype.val

instance pairPrime_maximal (I J : Ideal ActualEisensteinCubic.O) (P : PrimeIndex I ⊕ PrimeIndex J) :
    (pairPrime I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

section
variable (I J : Ideal ActualEisensteinCubic.O) (hI : Admissible I) (hJ : Admissible J)

include hI hJ in
lemma pairPrime_good      
     P  : goodLambda ∉ pairPrime I J P := by
  cases P with
  | inl P => exact primeIndex_good I hI.2 P
  | inr P => exact primeIndex_good J hJ.2 P

include hI hJ in
lemma pairPrime_coprime      
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (pairPrime I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
      (primeIndex_le J (primaryGenerator_ne_zero_ideal J hJ.2) Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

include hI hJ in
lemma pairPrime_product       :
    (∏ P, pairPrime I J P) = I * J := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (primeIndex_product I hI) (primeIndex_product J hJ)

end

def pairExponent (I J ) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (fun _ => 4) (fun _ => 2)

section
variable (I J : Ideal ActualEisensteinCubic.O) (hI : Admissible I) (hJ : Admissible J) (z : ActualEisensteinCubic.O)

lemma pairExponent_nonprincipal      
     P  :
    actualSextic (pairPrime I J P) (pairPrime_good I J hI hJ P) ^ pairExponent I J P ≠ 1 := by
  cases P with
  | inl P => exact cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) true
  | inr P => exact cubicExponent_nonprincipal P.val (primeIndex_good J hJ.2 P) false

lemma primeIndex_cubic_row       :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z =
      cubicRow I z := (CompletedGauss.cubicRow_mk I hI.2 z).symm.trans
    (CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z)

lemma primeIndex_conjugate_cubic_row       :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      star (cubicRow I z) := by
  have he : finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      (finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z) ^ 2 := by
    simp only [finiteSexticRow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro P hP
    rw [MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0),
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ← pow_mul]
  rw [he, primeIndex_cubic_row I hI, cubicRow_square_eq_star]

lemma pairPrime_row         :
    finiteSexticRow (pairPrime I J) (pairPrime_good I J hI hJ) (pairExponent I J) z =
      star (cubicRow I z) * cubicRow J z := by
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (primeIndex_good J hJ.2) (fun _ => 2) z = _
  rw [primeIndex_conjugate_cubic_row I hI, primeIndex_cubic_row J hJ]

include hI hJ in
lemma pairPrime_modulus       :
    Ideal.span {primaryGenerator I * primaryGenerator J} = ∏ P, pairPrime I J P := by
  rw [pairPrime_product I J hI hJ, ← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]

end

end
end SevenEighths.CubicSieve

end OAI
