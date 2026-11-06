module

public import OAI.NumberTheory.DirichletL.Reflection.CoprimeSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : ActualEisensteinCubic.O} {mode : Bool}

def finitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (S : Ideal ActualEisensteinCubic.O→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal ActualEisensteinCubic.O) (hK : Admissible K)
    (S : Ideal ActualEisensteinCubic.O→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal ActualEisensteinCubic.O→ℂ) (w₀ : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

end
end SevenEighths.InverseReflectedPhase

end OAI
