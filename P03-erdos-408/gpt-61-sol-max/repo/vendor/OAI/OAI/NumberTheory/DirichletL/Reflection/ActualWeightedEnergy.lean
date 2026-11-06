module

public import OAI.NumberTheory.DirichletL.Reflection.WeightedEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section


variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : ActualEisensteinCubic.O} {mode : Bool}

def weightedReflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal ActualEisensteinCubic.O → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (r aw : Ideal ActualEisensteinCubic.O → ℂ) (w : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O)) (K : Ideal ActualEisensteinCubic.O)  :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K*r K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m*aw P)
      (frozenBranchColumn F jF e (fun n b => A n b*w n b)) K

end
end SevenEighths.InverseReflectedPhase

end OAI
