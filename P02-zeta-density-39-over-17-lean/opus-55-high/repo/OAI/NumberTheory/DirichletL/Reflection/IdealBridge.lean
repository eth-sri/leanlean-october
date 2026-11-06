module
public import OAI.NumberTheory.DirichletL.Reflection.Branch
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance idealBridgeFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

section
variable (K : Ideal Eis) (hK : Admissible K)
include K hK
theorem admissible_primeIndex_product :
    (∏ P : PrimeIndex K, P.val) = K := by
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hK.1).mp hK.2.1
  pm_5544 CompletedGauss.primeSupport K UniqueFactorizationMonoid.normalizedFactors hn.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport K, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport K).val.prod := (Finset.prod_val _).symm
    _ = K := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hK.1

theorem idealRowHom_cube_eq_quadratic (z : Eis) :
    idealRowHom z K ^ 3 = quadraticRow K z := by
  conv_lhs => rw [← admissible_primeIndex_product K hK,map_prod,← Finset.prod_pow]
  rw [quadraticRow_eq_primeIndex K hK]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ) ≠ 0)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime z P.val (admissiblePrimeGood K hK P)]
end

section
variable {ι : Type*} [Fintype ι] (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
include ι P hg
theorem residual_bracket_finset (R : Finset ι) (hR : Admissible (∏ i ∈ R, P i))
    (n b : Ideal Eis) :
    (∏ i ∈ R, bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) =
      idealRowHom (primaryGenerator (n*b)) (P i)^3 := by
    have he := residual_bracket_cube (P i) (hg i) 1 (primaryGenerator n) (primaryGenerator b)
    simpa only [one_mul,map_one,one_pow,primaryGenerator_mul,idealRowHom_prime _ (P i) (hg i)] using he
  simp_rw [hl]
  rw [Finset.prod_pow,← map_prod,idealRowHom_cube_eq_quadratic _ hR]

theorem marked_bracket_finset (S : Finset ι) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  have he := marked_bracket_hybrid (fun i : S => P i.val) (fun i => hg i.val) n b hb
  have hl : (∏ i : S, bracket (actualSextic (P i.val) (hg i.val)) 0
      (Ideal.Quotient.mk (P i.val) (primaryGenerator n*(primaryGenerator b)^3))) =
      ∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) := by
    exact Finset.prod_coe_sort S (fun i => bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)))
  pm_293 hl he Finset.prod_coe_sort

theorem full_branch_sum_hybrid (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hSj : ∀ i ∈ S, j i = 0)
    (hR : Admissible (∏ i ∈ R, P i)) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∑ e : ι → Fin 3, reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)) =
      (∏ i ∈ F, bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  trans ∏ i, bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  · exact (prod_bracket_eq_full_branches P hg j (primaryGenerator n) (primaryGenerator b)).symm
  let v := fun i => bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  have hr : (∏ i ∈ R, v i) = quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
    rw [← residual_bracket_finset P hg R hR n b]
    pm_7997 hRj
  have hs : (∏ i ∈ S, v i) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
    rw [← marked_bracket_finset P hg S n b hb]
    pm_7997 hSj
  have hv : (∏ i, v i) = (∏ i ∈ R, v i)*(∏ i ∈ S, v i)*(∏ i ∈ F, v i) := by
    pm_8754 hRS
  change (∏ i, v i) = _
  rw [hv,hr,hs]
  ring
end

end
end SevenEighths.InverseReflectedPhase

end OAI
