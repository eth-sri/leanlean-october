module

public import OAI.NumberTheory.DirichletL.Reflection.Energy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : ActualEisensteinCubic.O} {mode : Bool}

theorem masked_actual_coefficient (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (S : PrimeFamily σ) (P : Ideal ActualEisensteinCubic.O) (hprod : (∏ i, S.ideal i) = P) (jF : φ → ℕ)
    (D : IsCoprime K P → ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (hcop : IsCoprime K P → Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ h, (D h).fixedFactor = D0.fixedFactor)
    (hA : ∀ h u m n b, actualCuspColumn (D h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : Ideal ActualEisensteinCubic.O) (hb : primaryGenerator b ≠ 0) :
    (if h : IsCoprime K P then actualMixedCoefficient F K hK S jF (D h) s hc u m n b else 0) =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
          actualRowPhaseExtension F jF s u m K)*
        (actualSlotPhase F S jF s u m / (Real.sqrt (Ideal.absNorm P:ℝ):ℂ))*
        (if IsCoprime K P then 1 else 0)*
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m) n b*
          quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
          (if IsCoprime P b then 1 else 0)) := by
  by_cases hKP : IsCoprime K P
  · rw [dite_eq_left hKP]
    have hh := actualMixedCoefficient_common_branches F K hK S jF (D hKP) s hc (hcop hKP)
      D0.fixedFactor (actualCuspColumn D0 s hc) (by grind) (hA hKP) u m n b hb
    rw [hprod] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro e he
    rw [actualRowPhaseExtension,dite_eq_left hK,frozenBranchColumn_eq_normalized]
    ring
  simp_all

end
end SevenEighths.InverseReflectedPhase

end OAI
