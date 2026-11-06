module

public import OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment


variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : ActualEisensteinCubic.O} {mode : Bool}

theorem actualMixedCoefficient_common_branches (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (κ : ℂ) (A : ActualEisensteinCubic.Oˣ → ℕ → Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (hκ : D.fixedFactor = κ)
    (hA : ∀ u m n b, actualCuspColumn D s hc u m n b = A u m n b)
     u   m   n b  (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*
          actualSlotPhase F S jF s u m*actualFrozenPhase F jF κ s u m)*
        (frozenBranchScale F jF e:ℂ)*normalizedFrozenColumn F jF e (A u m) n b*
        (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
        (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
        (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  rw [actualMixedCoefficient_factor F K hK S jF D s hc hcop u m n b hb,
    sourceFrozenPhase_eq_actual,hκ,sourceColumn_eq_sum_frozenBranches]
  have hfun : actualCuspColumn D s hc u m = A u m := funext (fun n => funext (hA u m n))
  rw [hfun,Finset.mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [frozenBranchColumn_eq_normalized]
  ring


end SevenEighths.InverseReflectedPhase

end OAI
