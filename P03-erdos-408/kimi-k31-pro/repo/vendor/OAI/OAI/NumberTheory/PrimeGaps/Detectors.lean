module

public import OAI.NumberTheory.PrimeGaps.EqualityPatterns

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics



open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem divisorSum_fin_zero (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    divisorSum X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [divisorSum,h,Finset.sum_singleton]
  simp only [divisorCoefficient,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i

end LargePrimeGaps

end OAI
