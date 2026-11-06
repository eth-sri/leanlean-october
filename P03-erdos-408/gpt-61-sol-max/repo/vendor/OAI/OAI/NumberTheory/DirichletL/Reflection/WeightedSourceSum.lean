module

public import OAI.NumberTheory.DirichletL.Reflection.ActualWeightedEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : ActualEisensteinCubic.O} {mode : Bool}

def weightedPhysicalReflectedRow (F : PrimeFamily φ) (K ) (hK )
    (S : Ideal ActualEisensteinCubic.O → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal ActualEisensteinCubic.O → ℂ) (w : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ)  :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K*aw P.val*w n b*(if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0)

theorem weightedPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (S : Ideal ActualEisensteinCubic.O → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
     s   hc 
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
     r aw   w   u   m  :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K := by
  unfold weightedPhysicalReflectedRow
  have he (P : Pset) (n : Ideal ActualEisensteinCubic.O) (b : Ideal ActualEisensteinCubic.O) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [weightedReflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  unfold frozenBranchColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
