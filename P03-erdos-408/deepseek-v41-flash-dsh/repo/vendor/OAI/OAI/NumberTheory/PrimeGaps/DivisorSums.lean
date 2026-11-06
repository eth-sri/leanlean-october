module

public import OAI.NumberTheory.PrimeGaps.Indices
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

namespace OAI

namespace LargePrimeGaps



noncomputable def logCoordinates {ι : Type*} (X : ℕ) (d : ι → ℕ) : ι → ℝ :=
  fun i => Real.log (d i : ℝ) / Real.log (X : ℝ)

noncomputable def divisorCoefficient {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * F (logCoordinates X d)

noncomputable def divisorSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (m : ℕ) (b : ι → ℕ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => (m + b i).divisors), divisorCoefficient X F d

end LargePrimeGaps

end OAI
