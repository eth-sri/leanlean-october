module
public import OAI.NumberTheory.DirichletL.CubicSieve.Ideal
public import OAI.NumberTheory.DirichletL.CubicSieve.Initial
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by pf_239 hI.2 hJ.2

theorem idealSymbol_eq_idealSexticRow_sq
    (F : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hI : I ∈ F) (hsq : Squarefree I) (z : O) :
    eisEmbedding (CubicJacobiGlobal.idealSymbol I z) =
      (idealSexticRow F hFp hFg I z) ^ 2 := by
  rw [← CanonicalRowCompletion.idealRowHom_square]
  congr 1
  pm_1477 hFp
  conv_lhs => rw [← idealSupport_product_eq F hI hsq, map_prod]
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_congr rfl
  intro i hi
  exact CanonicalRowCompletion.idealRowHom_prime z i.val (primePool_good F hFg i)

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  pm_7214
  pm_3820
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    pm_136 z hz I hI Finset.mem_image.mp
    rw [primaryGenerator_norm_sq I ((mem_idealRange.mp hI).1.2)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_cubic_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (idealMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    pm_1301
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      (idealSexticRow F hFp hFg J.val z) ^ 2 * a J
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, eisEmbedding (CubicJacobiGlobal.idealSymbol J.val (primaryGenerator I.val)) * a J‖ ^ 2 := by
    pm_3072
  pm_3071

end
end SevenEighths.CubicSieve

end OAI
