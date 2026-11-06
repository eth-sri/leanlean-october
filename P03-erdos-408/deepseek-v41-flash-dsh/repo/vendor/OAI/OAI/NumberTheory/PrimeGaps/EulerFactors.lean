module

public import OAI.NumberTheory.PrimeGaps.ZetaKernel
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

namespace OAI

namespace LargePrimeGaps













noncomputable def primeMonomial {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) : ℂ :=
  Complex.exp (-(Real.log p : ℂ)*(∑ i∈S, z i))

@[simp] theorem primeMonomial_zero {ι : Type*} (p : ℕ) (S : Finset ι) :
    primeMonomial p (fun _ => (0:ℂ)) S = 1 := by simp [primeMonomial]

end LargePrimeGaps

end OAI
