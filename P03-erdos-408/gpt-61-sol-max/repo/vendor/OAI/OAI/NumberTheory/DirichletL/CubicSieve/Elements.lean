module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.Extraction

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section


def elementCharacter (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I ≠ 0) : ActualEisensteinCubic.O →* ℂ where
  toFun x := eisEmbedding (CubicJacobiGlobal.idealSymbol I x)
  map_one' := by rw [CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' x y := by rw [CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem elementCharacter_norm_le_one  I   hI   x  :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal ActualEisensteinCubic.O) (B : b → Ideal ActualEisensteinCubic.O) (D : c → ActualEisensteinCubic.O)
    (cols : n → Ideal ActualEisensteinCubic.O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

def goodPart (I : Ideal ActualEisensteinCubic.O)  := CanonicalQuadraticSieve.goodSquarefreePart I

def badPart (I : Ideal ActualEisensteinCubic.O)  :=
  ∏ P ∈ CanonicalQuadraticSieve.badPrimeSupport I, P

theorem goodPart_admissible  I  : Admissible (goodPart I) := by
  have h := CanonicalQuadraticSieve.goodSquarefreePart_admissible I
  exact ⟨h.2.1, CanonicalQuadraticSieve.primaryGenerator_admissible _ h⟩

theorem badPart_mul_goodPart  I  (hI : Squarefree I) :
    badPart I * goodPart I = I := CanonicalQuadraticSieve.squarefree_bad_good_product I hI

def extractedGenerator (I : Ideal ActualEisensteinCubic.O)  :=
  primaryGenerator (goodPart (firstPart I)) *
    primaryGenerator (goodPart (secondPart I)) ^ 2 *
    idealGenerator (cubePart I) ^ 3 *
    (idealGenerator (badPart (firstPart I)) * idealGenerator (badPart (secondPart I)) ^ 2)

theorem span_extractedGenerator  I  (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {idealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {idealGenerator (badPart (firstPart I))} *
      Ideal.span {idealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_idealGenerator, span_idealGenerator, span_idealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      ring
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction  z  (hz : z ≠ 0) :
    ∃ u : ActualEisensteinCubic.Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal ActualEisensteinCubic.O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector  I  :
    ∃ E : CanonicalQuadraticSieve.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := ⟨⟨CanonicalQuadraticSieve.badPrimeSupport I,
    Finset.mem_powerset.mpr (CanonicalQuadraticSieve.badPrimeSupport_subset I)⟩, rfl⟩

end
end SevenEighths.CubicSieve

end OAI
